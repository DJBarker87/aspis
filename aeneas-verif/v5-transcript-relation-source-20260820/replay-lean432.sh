#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5TranscriptRelationHelper"
readonly proof="$bundle/proof/V5TranscriptRelationSourceProof.lean"
readonly final_join_proof="$bundle/proof/V5TranscriptRelationFinalJoin.lean"
readonly import_normalization_patch="$bundle/import-normalization/V5RelationCallerGenerated-for-join.patch"
readonly harness="$bundle/relation-harness"
readonly acceptance_bundle="$root/aeneas-verif/v5-relation-acceptance-20260815"
readonly acceptance_caller="$acceptance_bundle/generated/V5RelationCallerGenerated.lean"
readonly acceptance_proof="$acceptance_bundle/proof/V5RelationAcceptanceSourceProof.lean"

readonly lean_bin="${LEAN432_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}"
readonly lake_bin="${LAKE432_BIN:-$(dirname "$lean_bin")/lake}"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to patched Aeneas 000c7b6a}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/target/release/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/src/_build/default/main.exe}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Aeneas Lean 4.32 library}"
readonly aeneas_path="${AENEAS_LEAN_PATH:-$aeneas_lib}"
readonly formal_build_root="${ASPIS_FORMAL_BUILD_ROOT:-$root}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="000c7b6a4ab001ddceb16a82dd7fd37c3abfe24d"
readonly expected_charon_sha256="7fad09bfb0e4e6a52472175a6414f65fcb790918658915785088f86c6231ba1a"
readonly expected_aeneas_sha256="2994c7ed152546b20ca44506ea61c554b93ab806acefe38af905c6f89e4dde84"

check_blob() {
  local expected=$1
  local path=$2
  local actual
  actual=$(git -C / hash-object --no-filters "$root/$path")
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

# These blobs bind the replay to the exact unchanged production helper and
# package graph reviewed for this proof bundle.
check_blob ca28d560e44e5e82e689321f32289831c889a0bd \
  programs/aspis-verifier/src/v5_cu_probe.rs
check_blob e2a5b6412e9410ffd1e392d8ea32033aab76f83f \
  aeneas-verif/v5-transcript-relation-source-20260820/relation-harness/Cargo.toml
check_blob 728dc91c3f1f9d6443df8b793c617b340a2e2a45 \
  aeneas-verif/v5-transcript-relation-source-20260820/relation-harness/Cargo.lock
check_blob a1d3b661d4cae680027fd2236422042774c66d94 \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/TypesExternal.lean
check_blob e8e80f86c38a2a5562330b34fd53f2defc840ebe \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/FunsExternal.lean
check_blob ff2c2318274298244b47e01e2ca1690a7435ff3c \
  aeneas-verif/v5-relation-acceptance-20260815/generated/V5RelationCallerGenerated.lean
check_blob 61044bf7ada9152f33aa1e228761c159d7fcca46 \
  aeneas-verif/v5-relation-acceptance-20260815/proof/V5RelationAcceptanceSourceProof.lean
check_blob bd965e686efa6c2b4bd29c16efc173a3dc7ab688 \
  aeneas-verif/v5-transcript-relation-source-20260820/import-normalization/V5RelationCallerGenerated-for-join.patch
check_blob cf809590ce8f89ac83b1e72f4e7ec0a80081d72b \
  aeneas-verif/v5-transcript-relation-source-20260820/proof/V5TranscriptRelationFinalJoin.lean
check_blob 8ca023e0a55d300c3ff22690c162b2dc4f1502cc \
  AspisFormal/AspisFormal/V5TranscriptConnection.lean
check_blob 92d4a73b86b80cad89365610172e1687fecb2c05 \
  AspisFormal/AspisFormal/V5TranscriptSourceAdapter.lean

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
readonly formal_overlay="$out/formal-overlay"
readonly join_source="$out/join-source"
readonly log="$out/replay.log"
mkdir -p "$source_root/programs/aspis-verifier" \
  "$source_root/aeneas-verif/v5-transcript-relation-source-20260820" \
  "$raw" "$normalized" "$olean/V5TranscriptRelationHelper" \
  "$formal_overlay/AspisFormal" "$join_source"
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
    --include \
      aspis_verifier_kappa_caller_extraction::v5_cu_probe::private_openings::V5PrivateOpeningRoots \
    --opaque aspis_core::transcript::Transcript \
    --opaque aspis_core::field \
    --opaque core::cmp \
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

formal_path=$(cd "$formal_build_root/AspisFormal" && \
  NO_DNA=1 "$lake_bin" env printenv LEAN_PATH)
readonly formal_path

formal_package_dir=
old_ifs=$IFS
IFS=:
for candidate in $formal_path; do
  if [[ -f "$candidate/AspisFormal/V5NonceWorkAuthentication.olean" ]]; then
    formal_package_dir="$candidate/AspisFormal"
    break
  fi
done
IFS=$old_ifs
readonly formal_package_dir
[[ -n "$formal_package_dir" ]]
for existing in "$formal_package_dir"/*; do
  ln -s "$existing" "$formal_overlay/AspisFormal/"
done
rm -f "$formal_overlay/AspisFormal/V5TranscriptConnection.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptConnection.ilean" \
  "$formal_overlay/AspisFormal/V5TranscriptConnection.c" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.ilean" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.c"

compile() {
  local target=$1
  local source=$2
  echo "COMPILE $target" | tee -a "$log"
  LEAN_PATH="$olean:$bundle/generated:$formal_overlay:$formal_path:$aeneas_path" \
    "$lean_bin" -j 1 -o "$olean/$target.olean" "$source" >> "$log" 2>&1
}

compile V5TranscriptRelationHelper/TypesExternal \
  "$generated/TypesExternal.lean"
compile V5TranscriptRelationHelper/Types "$generated/Types.lean"
compile V5TranscriptRelationHelper/FunsExternal \
  "$generated/FunsExternal.lean"
compile V5TranscriptRelationHelper/Funs "$generated/Funs.lean"
compile V5TranscriptRelationSourceProof "$proof"

# Rebuild the two maintained transcript modules used by the cross-bundle
# theorem. Compile the first outside the sparse overlay namespace so Lean
# resolves its earlier dependencies from the selected formal build.
echo "COMPILE AspisFormal/V5TranscriptConnection" | tee -a "$log"
LEAN_PATH="$formal_overlay:$formal_path:$aeneas_path" \
  "$lean_bin" -j 1 -o "$out/V5TranscriptConnection.olean" \
  "$root/AspisFormal/AspisFormal/V5TranscriptConnection.lean" >> "$log" 2>&1
mv "$out/V5TranscriptConnection.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptConnection.olean"

echo "COMPILE AspisFormal/V5TranscriptSourceAdapter" | tee -a "$log"
LEAN_PATH="$formal_overlay:$formal_path:$aeneas_path" \
  "$lean_bin" -j 1 -o "$out/V5TranscriptSourceAdapter.olean" \
  "$root/AspisFormal/AspisFormal/V5TranscriptSourceAdapter.lean" >> "$log" 2>&1
mv "$out/V5TranscriptSourceAdapter.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.olean"

# Keep both Aeneas snapshots byte-for-byte exact in the repository.  Their
# independently generated ProgramError enums ask Lean's discriminant macro for
# the same process-global instance name, even though neither joined theorem
# computes that discriminant.  Apply the reviewed one-line import normalization
# only to a temporary copy of the relation caller.
cp "$acceptance_caller" "$join_source/V5RelationCallerGenerated.lean"
git -C "$join_source" init -q
git -C "$join_source" apply --check "$import_normalization_patch"
git -C "$join_source" apply "$import_normalization_patch"
normalized_caller_blob=$(git -C / hash-object --no-filters \
  "$join_source/V5RelationCallerGenerated.lean")
if [[ "$normalized_caller_blob" != \
    "c9d60c817e396e94011b9afafd68d95bed2b8c15" ]]; then
  echo "unexpected relation-caller import normalization" >&2
  exit 1
fi

echo "COMPILE V5RelationCallerGenerated" | tee -a "$log"
(
  cd "$join_source"
  LEAN_PATH="$olean:$bundle/generated:$formal_overlay:$formal_path:$aeneas_path" \
    "$lean_bin" -j 1 -o "$olean/V5RelationCallerGenerated.olean" \
    V5RelationCallerGenerated.lean >> "$log" 2>&1
)
compile V5RelationAcceptanceSourceProof "$acceptance_proof"
compile V5TranscriptRelationFinalJoin "$final_join_proof"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' \
    "$generated" "$proof" "$final_join_proof" "$acceptance_proof" \
    "$root/AspisFormal/AspisFormal/V5TranscriptConnection.lean" \
    "$root/AspisFormal/AspisFormal/V5TranscriptSourceAdapter.lean"; then
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
