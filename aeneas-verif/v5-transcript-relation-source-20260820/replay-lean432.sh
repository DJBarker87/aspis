#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5TranscriptRelationHelper"
readonly proof="$bundle/proof/V5TranscriptRelationSourceProof.lean"
readonly extraction_patch="$bundle/extraction/v5-relation-replay-while.patch"
readonly harness="$bundle/relation-harness"

readonly lean_bin="${LEAN432_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas 9a30bf93}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/src/_build/default/main.exe}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Aeneas Lean 4.32 library}"
readonly aeneas_path="${AENEAS_LEAN_PATH:-$aeneas_lib}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="9a30bf93807d8043a1a968b6456eb78747c81cb4"
readonly expected_charon_sha256="776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375"
readonly expected_aeneas_sha256="278d7905bdccc469ae0760b991bbaff94062e2983a02f35262e4acee51f0976b"

check_blob() {
  local expected=$1
  local path=$2
  local actual
  actual=$(git -C "$root" hash-object "$path")
  if [[ "$actual" != "$expected" ]]; then
    echo "source identity mismatch: $path" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 1
  fi
}

check_sha256() {
  local expected=$1
  local path=$2
  local actual
  actual=$(shasum -a 256 "$path" | awk '{print $1}')
  if [[ "$actual" != "$expected" ]]; then
    echo "binary identity mismatch: $path" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 1
  fi
}

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
case "$(rustc +nightly-2026-06-01 --version)" in
  "rustc 1.98.0-nightly (14210df0e 2026-05-31)") ;;
  *) echo "expected Rust nightly-2026-06-01" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Data/Discriminant.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/RustAttributes.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/Simp/SimpScalar.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
check_sha256 "$expected_charon_sha256" "$charon_bin"
check_sha256 "$expected_aeneas_sha256" "$aeneas_bin"

# These blobs bind the replay to the exact production helper, extraction-only
# transformation, and package graph reviewed for this proof bundle.
check_blob ca28d560e44e5e82e689321f32289831c889a0bd \
  programs/aspis-verifier/src/v5_cu_probe.rs
check_blob 3b4c5c4ca145cd87e9199b3ea9069d714d5f5e2d \
  aeneas-verif/v5-transcript-relation-source-20260820/extraction/v5-relation-replay-while.patch
check_blob e2a5b6412e9410ffd1e392d8ea32033aab76f83f \
  aeneas-verif/v5-transcript-relation-source-20260820/relation-harness/Cargo.toml
check_blob 728dc91c3f1f9d6443df8b793c617b340a2e2a45 \
  aeneas-verif/v5-transcript-relation-source-20260820/relation-harness/Cargo.lock
check_blob 6988356d4007fe3c059300e2ac0b3e43a563cc7c \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/TypesExternal.lean
check_blob 8ba03a7063c20bdc395662887bb0439cdb2e8872 \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/FunsExternal.lean

if [[ -n "${V5_TRANSCRIPT_RELATION_REPLAY_OUT:-}" ]]; then
  out=$V5_TRANSCRIPT_RELATION_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-transcript-relation-replay.XXXXXX)
fi
readonly out
readonly source_root="$out/source-root"
readonly replay_harness="$source_root/aeneas-verif/v5-transcript-relation-source-20260820/relation-harness"
readonly vendor="$out/vendor"
readonly llbc="$out/V5TranscriptRelationHelper.llbc"
readonly raw="$out/raw"
readonly normalized="$out/normalized"
readonly olean="$out/olean"
readonly log="$out/replay.log"
mkdir -p "$source_root/programs/aspis-verifier" \
  "$source_root/aeneas-verif/v5-transcript-relation-source-20260820" \
  "$raw" "$normalized" "$olean/V5TranscriptRelationHelper"
: > "$log"

# Work in a temporary tree.  The production checkout is never modified.
cp -R "$root/programs/aspis-verifier/src" \
  "$source_root/programs/aspis-verifier/src"
cp -R "$harness" "$replay_harness"
# The copied verifier is the extraction target.  Keep the two unchanged Rust
# libraries in their real workspace so their `*.workspace = true` manifest
# fields still resolve through the repository's root Cargo.toml.
ASPIS_REPLAY_ROOT="$root" perl -0pi -e '
  s{aspis-core = \{ path = "\.\./\.\./\.\./crates/aspis-core" \}}
   {aspis-core = { path = "$ENV{ASPIS_REPLAY_ROOT}/crates/aspis-core" }};
  s{aspis-statement = \{ path = "\.\./\.\./\.\./crates/aspis-statement" \}}
   {aspis-statement = { path = "$ENV{ASPIS_REPLAY_ROOT}/crates/aspis-statement" }};
' "$replay_harness/Cargo.toml"
git -C "$source_root" init -q
git -C "$source_root" apply --check "$extraction_patch"
git -C "$source_root" apply "$extraction_patch"

# Charon's pinned Rust frontend needs two host-only compatibility edits in
# solana-program 2.3.0.  They affect dependency compilation, not extracted
# Aspis definitions, and are reproduced here rather than hidden in a cache.
(
  cd "$replay_harness"
  cargo vendor --locked "$vendor" >> "$log" 2>&1
)
perl -0pi -e 's/    "cdylib",\n//' "$vendor/solana-program/Cargo.toml"
perl -pi -e \
  's/\Qassert_eq!((*(*data_ptr).as_ptr())[..], data[..]);\E/assert_eq!((\&(*(*data_ptr).as_ptr()))[..], data[..]);/' \
  "$vendor/solana-program/src/program.rs"
grep -Fq 'assert_eq!((&(*(*data_ptr).as_ptr()))[..], data[..]);' \
  "$vendor/solana-program/src/program.rs"
if rg -q '^    "cdylib",$' "$vendor/solana-program/Cargo.toml"; then
  echo "failed to remove host-incompatible solana-program cdylib target" >&2
  exit 1
fi

echo "EXTRACT production relation transcript helper" | tee -a "$log"
(
  cd "$replay_harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      aspis_verifier_kappa_caller_extraction::v5_cu_probe::replay_real_v5_relation_rounds \
    --opaque aspis_verifier_kappa_caller_extraction::v5_cu_probe \
    --include \
      aspis_verifier_kappa_caller_extraction::v5_cu_probe::replay_real_v5_relation_rounds \
    --include \
      aspis_verifier_kappa_caller_extraction::v5_cu_probe::ParsedProbeData \
    --opaque aspis_core::transcript::Transcript \
    --opaque aspis_core::field \
    --opaque core::cmp \
    --exclude core::iter \
    --exclude core::slice::iter \
    --dest-file "$llbc" -- --offline \
    --config "patch.crates-io.solana-program.path=\"$vendor/solana-program\""
) >> "$log" 2>&1

echo "TRANSLATE extracted helper to Lean" | tee -a "$log"
"$aeneas_bin" -backend lean \
  -namespace V5TranscriptRelationGenerated \
  -split-files -no-progress-bar -dest "$raw" "$llbc" >> "$log" 2>&1

normalize_generated() {
  local kind=$1
  local source=$2
  local destination=$3
  if [[ "$kind" == "types" ]]; then
    perl -0777 -pe '
      s/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Data.Discriminant\n/;
      s{Source: '\''[^'\''\n]*/(crates|programs)/}{Source: '\''$1/}g;
      s{Source: '\''/cargo/registry/src/[^/]+/}{Source: '\''registry/}g;
      s/[ \t]+$//mg;
    ' "$source" > "$destination"
  else
    perl -0777 -pe '
      s/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n/;
      s{Source: '\''[^'\''\n]*/(crates|programs)/}{Source: '\''$1/}g;
      s{Source: '\''/cargo/registry/src/[^/]+/}{Source: '\''registry/}g;
      s/[ \t]+$//mg;
    ' "$source" > "$destination"
  fi
}

compare_generated() {
  local kind=$1
  local regenerated=$2
  local checked=$3
  local name=$4
  local normalized_regenerated="$normalized/$name.regenerated.lean"
  local normalized_checked="$normalized/$name.checked.lean"
  normalize_generated "$kind" "$regenerated" "$normalized_regenerated"
  normalize_generated "$kind" "$checked" "$normalized_checked"
  if ! cmp -s "$normalized_regenerated" "$normalized_checked"; then
    echo "regenerated Lean differs: $name" >&2
    diff -u "$normalized_checked" "$normalized_regenerated" | sed -n '1,200p' || true
    exit 1
  fi
  echo "MATCH $name" | tee -a "$log"
}

compare_generated types "$raw/Types.lean" "$generated/Types.lean" Types
compare_generated funs "$raw/Funs.lean" "$generated/Funs.lean" Funs

compile() {
  local target=$1
  local source=$2
  echo "COMPILE $target" | tee -a "$log"
  LEAN_PATH="$olean:$bundle/generated:$aeneas_path" \
    "$lean_bin" -j 1 -o "$olean/$target.olean" "$source" >> "$log" 2>&1
}

compile V5TranscriptRelationHelper/TypesExternal \
  "$generated/TypesExternal.lean"
compile V5TranscriptRelationHelper/Types "$generated/Types.lean"
compile V5TranscriptRelationHelper/FunsExternal \
  "$generated/FunsExternal.lean"
compile V5TranscriptRelationHelper/Funs "$generated/Funs.lean"
compile V5TranscriptRelationSourceProof "$proof"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' \
    "$generated" "$proof"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in transcript relation replay" >&2
  exit 1
fi

echo "Lean 4.32 production relation-transcript extraction and proof replay: PASS"
echo "V5_TRANSCRIPT_RELATION_REPLAY_OUT=$out"
echo "log: $log"
