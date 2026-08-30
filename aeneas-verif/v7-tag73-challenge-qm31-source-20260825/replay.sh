#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=${REPO_ROOT:-$(cd "$script_dir/../.." && pwd)}

readonly deployed_commit=1589706d38a5e8ca705fbf7aaed2c82cf8595510
readonly deployed_core_tree=4a869518c17b226068499b7c7880e05212315cd6
readonly charon_commit=cb50ff16b9f1066b8a97dc06da704de2da2fa41c
readonly aeneas_commit=b59d5188c082f704a418c7cb4e52ad69328002d1
readonly expected_charon_sha=b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
readonly expected_aeneas_sha=4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5
readonly expected_patch_sha=5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c
readonly expected_aeneas_lean_sources_sha=b98335b2ce64c0e72730159fc86987dd456b8d8dace6dd7a2cd9f5ccf5946433
readonly expected_aeneas_lean_oleans_sha=cd6d2204d071615a7c386af875908c375f94a1f4bec456df49cc7b37fce11ef5
readonly expected_aspis_manifest_sha=65c23cce5c1bab2ba00affdff53fe52b67388cf2491c7f8ec68c1c2977dd7c10
readonly expected_schedule_sha=1e9ebd3c03cba109e1bbe7f677165fec523ce2b7b1e281301c5b2068dc164274
readonly expected_refinement_sha=126bcf5092c1b6671ba4a8d2259753043abb8e9d388d1c63447d48f6d6c43f43
readonly expected_decoder_sha=9fc5c4a3befadab4e3e8acf9103dfa324f66f62d6abe481390cbb7d6ec710293
readonly expected_compact_types_sha=f7f643caaee597aa0bf1b8147396fcef80ff1e8073db43c0db631deec5b8dd30
readonly expected_compact_funs_sha=73fefb4eee847570c37c230277f9c8526646a19a41522061580f41348dc1878e
readonly expected_harness_lock_sha=0d55f7976302de188725b2adacd1cfcc4d2dbdf0f905751358d8044dbf020bdb
readonly expected_llbc_sha=0c9f44a7a426b7efd1404e8776795958d89f203eca2915994d013a756b27d857
readonly expected_types_canonical_sha=2beae4347eb134ccfa73f56b471d278bbdfbcb2b56d14a10c6ac8976240d8e8c
readonly expected_funs_canonical_sha=2406554baf66146eb9d0434fdd65fbf78dad177e63f538e660f449e9c4c4b884

: "${CHARON_BIN:?set CHARON_BIN to the pinned Charon binary}"
: "${CHARON_ROOT:?set CHARON_ROOT to the pinned Charon checkout}"
: "${AENEAS_BIN:?set AENEAS_BIN to the pinned Aeneas binary}"
: "${AENEAS_SOURCE_ROOT:?set AENEAS_SOURCE_ROOT to the pinned Aeneas checkout}"
: "${AENEAS_LEAN_ROOT:?set AENEAS_LEAN_ROOT to the pinned Aeneas Lean backend}"
charon_bin=$CHARON_BIN
charon_root=$CHARON_ROOT
aeneas_bin=$AENEAS_BIN
aeneas_source_root=$AENEAS_SOURCE_ROOT
aeneas_lean_root=$AENEAS_LEAN_ROOT
aspis_formal_root=${ASPIS_FORMAL_ROOT:-$repo_root/AspisFormal}
lean_bin=${LEAN_BIN:-$(command -v lean || true)}
compact_bundle=${COMPACT_BUNDLE_ROOT:-$repo_root/aeneas-verif/v7-tag73-compact-semantic-source-20260825/generated-full/V7CompactSemanticChallengeOpaqueNoDedup}
formal_k1=${FORMAL_K1_ROOT:-$repo_root/AspisFormal/AspisFormal/K1}
export CARGO_BUILD_JOBS=1
export LEAN_NUM_THREADS=1

while read -r expected_mode relative_path; do
  [[ "$expected_mode" =~ ^0[0-7]{3}$ ]]
  [[ "$relative_path" == ./* ]]
  executable="$script_dir/${relative_path#./}"
  [[ -f "$executable" ]]
  actual_mode=$(stat -c '%a' "$executable")
  if [[ "0$actual_mode" != "$expected_mode" ]]; then
    printf 'executable mode mismatch: %s expected %s, found 0%s\n' \
      "$relative_path" "$expected_mode" "$actual_mode" >&2
    exit 1
  fi
done < "$script_dir/FILE-MODES.manifest"

[[ $(git -C "$charon_root" rev-parse HEAD) == "$charon_commit" ]]
[[ $(git -C "$aeneas_source_root" rev-parse "$aeneas_commit") == "$aeneas_commit" ]]
echo "$expected_charon_sha  $charon_bin" | sha256sum -c -
echo "$expected_aeneas_sha  $aeneas_bin" | sha256sum -c -
echo "$expected_patch_sha  $repo_root/aeneas-verif/lean432/aeneas-b59d5188-lean432.patch" |
  sha256sum -c -
file "$aeneas_bin" | rg 'ELF 64-bit.*x86-64.*statically linked'
[[ $("$aeneas_bin" -version) == 'aeneas b59d5188-lean432-extended' ]]
case $("$lean_bin" --version) in
  'Lean (version 4.32.0,'*) ;;
  *) echo 'expected Lean 4.32.0' >&2; exit 1 ;;
esac

actual_aeneas_lean_sources_sha=$(
  cd "$aeneas_lean_root"
  find Aeneas -type f -name '*.lean' -print0 |
    sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}'
)
[[ "$actual_aeneas_lean_sources_sha" == "$expected_aeneas_lean_sources_sha" ]]
actual_aeneas_lean_oleans_sha=$(
  cd "$aeneas_lean_root"
  find .lake/build/lib/lean/Aeneas -type f -name '*.olean' -print0 |
    sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}'
)
[[ "$actual_aeneas_lean_oleans_sha" == "$expected_aeneas_lean_oleans_sha" ]]
echo "$expected_aspis_manifest_sha  $aspis_formal_root/lake-manifest.json" |
  sha256sum -c -
echo "$expected_schedule_sha  $formal_k1/V7Tag73TranscriptSchedule.lean" |
  sha256sum -c -
echo "$expected_refinement_sha  $formal_k1/V7Tag73DeterministicRefinement.lean" |
  sha256sum -c -
echo "$expected_decoder_sha  $formal_k1/V7Tag73SamplerDecoder.lean" |
  sha256sum -c -
echo "$expected_compact_types_sha  $compact_bundle/Types.lean" |
  sha256sum -c -
echo "$expected_compact_funs_sha  $compact_bundle/Funs.lean" |
  sha256sum -c -
echo "$expected_harness_lock_sha  $script_dir/harness/Cargo.lock" |
  sha256sum -c -
[[ $(rg -n '^\[workspace\]$' "$script_dir/harness/Cargo.toml" | wc -l) -eq 1 ]]

replay_tmp=$(mktemp -d)
trap 'rm -rf -- "$replay_tmp"' EXIT
source_root="$replay_tmp/source"
harness="$source_root/aeneas-verif/v7-tag73-challenge-qm31-source-20260825/harness"
llbc="$replay_tmp/V7Tag73ChallengeQm31Full.llbc"
raw_parent="$replay_tmp/raw-generated"
raw_generated="$raw_parent"
checked="$replay_tmp/checked"
generated_olean="$replay_tmp/generated-olean"
formal_olean="$replay_tmp/formal-olean"
proof_olean="$replay_tmp/proof-olean"
root_checked="$replay_tmp/root-checked/V7CompactSemanticChallengeOpaqueNoDedup"
root_olean="$replay_tmp/root-olean"

mkdir -p "$source_root" "$harness" "$raw_parent" \
  "$checked/V7Tag73ChallengeQm31" \
  "$generated_olean/V7Tag73ChallengeQm31" \
  "$formal_olean/AspisFormal/K1" "$proof_olean" \
  "$root_checked" "$root_olean/V7CompactSemanticChallengeOpaqueNoDedup"

if [[ -n ${DEPLOYED_SOURCE_ROOT:-} ]]; then
  cp "$DEPLOYED_SOURCE_ROOT/Cargo.toml" "$source_root/"
  mkdir -p "$source_root/crates"
  cp -R "$DEPLOYED_SOURCE_ROOT/crates/aspis-core" "$source_root/crates/"
else
  [[ $(git -C "$repo_root" rev-parse "$deployed_commit") == "$deployed_commit" ]]
  [[ $(git -C "$repo_root" rev-parse "$deployed_commit:crates/aspis-core") == "$deployed_core_tree" ]]
  git -C "$repo_root" archive "$deployed_commit" -- \
    Cargo.toml Cargo.lock crates/aspis-core | tar -x -C "$source_root"
fi
# The harness declares its own nested workspace, so this frozen lockfile owns
# dependency resolution.  A top-level lockfile is neither read nor required.
cp -R "$script_dir/harness/." "$harness/"
(
  cd "$source_root"
  sha256sum -c "$script_dir/DEPLOYED-SOURCE.sha256"
)

export CARGO_TARGET_DIR="$replay_tmp/charon-target"
cargo check --manifest-path "$harness/Cargo.toml" --locked
(
  cd "$harness"
  "$charon_bin" cargo --preset aeneas --mir built \
    --start-from v7_tag73_challenge_qm31_source::extract_challenge_qm31 \
    --include aspis_core::transcript \
    --dest-file "$llbc" -- \
    --manifest-path "$harness/Cargo.toml" --lib
)

bundled_pre_mir="$replay_tmp/bundled.pre-mir.canonical.llbc.json"
replayed_pre_mir="$replay_tmp/replayed.pre-mir.canonical.llbc.json"
perl "$script_dir/normalization/canonicalize-llbc.pl" --preserve-mir \
  "$script_dir/extraction/V7Tag73ChallengeQm31Full.llbc" \
  > "$bundled_pre_mir"
perl "$script_dir/normalization/canonicalize-llbc.pl" --preserve-mir "$llbc" \
  > "$replayed_pre_mir"
perl "$script_dir/normalization/assert-mir-only-drift.pl" \
  "$bundled_pre_mir" "$replayed_pre_mir"

bundled_canonical_llbc="$replay_tmp/bundled.canonical.llbc.json"
canonical_llbc="$replay_tmp/replayed.canonical.llbc.json"
perl "$script_dir/normalization/canonicalize-llbc.pl" \
  "$script_dir/extraction/V7Tag73ChallengeQm31Full.llbc" \
  > "$bundled_canonical_llbc"
perl "$script_dir/normalization/canonicalize-llbc.pl" "$llbc" \
  > "$canonical_llbc"
cmp "$bundled_canonical_llbc" "$canonical_llbc"
actual_llbc_sha=$(sha256sum "$canonical_llbc" | awk '{print $1}')
printf 'canonical LLBC actual:   %s\n' "$actual_llbc_sha"
printf 'canonical LLBC expected: %s\n' "$expected_llbc_sha"
if [[ -n ${DIAGNOSTICS_DIR:-} ]]; then
  mkdir -p "$DIAGNOSTICS_DIR"
  cp "$llbc" "$DIAGNOSTICS_DIR/replayed.raw.llbc"
  cp "$bundled_pre_mir" \
    "$DIAGNOSTICS_DIR/bundled.pre-mir.canonical.llbc.json"
  cp "$replayed_pre_mir" \
    "$DIAGNOSTICS_DIR/replayed.pre-mir.canonical.llbc.json"
  cp "$canonical_llbc" "$DIAGNOSTICS_DIR/replayed.canonical.llbc.json"
  cp "$bundled_canonical_llbc" \
    "$DIAGNOSTICS_DIR/bundled.canonical.llbc.json"
fi
if [[ "$actual_llbc_sha" != "$expected_llbc_sha" ]]; then
  echo 'canonical LLBC mismatch' >&2
  exit 1
fi
if [[ ${STOP_AFTER_LLBC:-0} == 1 ]]; then
  echo 'V7 Tag-73 challenge_qm31 extraction/hash diagnostic: PASS'
  exit 0
fi

"$aeneas_bin" -backend lean -split-files \
  -namespace V7Tag73ChallengeQm31Generated \
  -dest "$raw_parent" -max-heartbeats 8000000 -max-recdepth 10000 "$llbc"

for expected_generated in Types Funs FunsExternal_Template; do
  [[ -f "$raw_generated/$expected_generated.lean" ]]
done

for generated_file in Types Funs; do
  perl "$script_dir/normalization/normalize-generated.pl" \
    "$raw_generated/$generated_file.lean" > "$replay_tmp/raw-$generated_file.canonical"
  perl "$script_dir/normalization/normalize-generated.pl" \
    "$script_dir/generated/V7Tag73ChallengeQm31/$generated_file.lean" > \
    "$replay_tmp/checked-$generated_file.canonical"
  cmp "$replay_tmp/raw-$generated_file.canonical" \
    "$replay_tmp/checked-$generated_file.canonical"
done
[[ $(sha256sum "$replay_tmp/raw-Types.canonical" | awk '{print $1}') == \
  "$expected_types_canonical_sha" ]]
[[ $(sha256sum "$replay_tmp/raw-Funs.canonical" | awk '{print $1}') == \
  "$expected_funs_canonical_sha" ]]

# The raw external template must contain exactly the two source constants;
# their checked definitions are copied from the bundle and compiled below.
mapfile -t external_axioms < <(
  rg -o 'axiom aspis_core[^ :]*' "$raw_generated/FunsExternal_Template.lean" |
    sed 's/^axiom //' | sort
)
[[ ${#external_axioms[@]} -eq 2 ]]
[[ ${external_axioms[0]} == aspis_core.field.M31.ZERO ]]
[[ ${external_axioms[1]} == aspis_core.field.P ]]

cp "$script_dir/generated/V7Tag73ChallengeQm31/Types.lean" \
  "$script_dir/generated/V7Tag73ChallengeQm31/FunsExternal.lean" \
  "$script_dir/generated/V7Tag73ChallengeQm31/Funs.lean" \
  "$checked/V7Tag73ChallengeQm31/"

aspis_lean_path=$(cd "$aspis_formal_root" && lake env printenv LEAN_PATH)
export LEAN_PATH="$generated_olean:$formal_olean:$aeneas_lean_root/.lake/build/lib/lean:$aspis_lean_path"
(
  cd "$checked"
  "$lean_bin" -o "$generated_olean/V7Tag73ChallengeQm31/Types.olean" \
    V7Tag73ChallengeQm31/Types.lean
  "$lean_bin" -o "$generated_olean/V7Tag73ChallengeQm31/FunsExternal.olean" \
    V7Tag73ChallengeQm31/FunsExternal.lean
  "$lean_bin" -o "$generated_olean/V7Tag73ChallengeQm31/Funs.olean" \
    V7Tag73ChallengeQm31/Funs.lean
)

for module in \
  V7Tag73TranscriptSchedule \
  V7Tag73DeterministicRefinement \
  V7Tag73SamplerDecoder \
  V7Tag73SamplerDecoderExact; do
  "$lean_bin" -o "$formal_olean/AspisFormal/K1/$module.olean" \
    "$formal_k1/$module.lean"
done
"$lean_bin" -o "$proof_olean/V7Tag73ChallengeQm31SourceCertificate.olean" \
  "$script_dir/proof/V7Tag73ChallengeQm31SourceCertificate.lean"

# Compile the callback replacement and then the unchanged compact generated
# Funs against it.  Normalization happens only in this temporary directory.
for root_file in Types Funs; do
  perl -pe 's/^import Aeneas$/import Aeneas.Std\nimport Aeneas.Data.Discriminant\nimport Aeneas.Tactic.RustAttributes/' \
    "$compact_bundle/$root_file.lean" > "$root_checked/$root_file.lean"
done
[[ $(rg -c '^import Aeneas$' "$root_checked/Types.lean" || true) -eq 0 ]]
for intended_import in \
  Aeneas.Std \
  Aeneas.Data.Discriminant \
  Aeneas.Tactic.RustAttributes; do
  [[ $(rg -c "^import $intended_import$" "$root_checked/Types.lean" || true) -eq 1 ]]
done
cp "$script_dir/replacement/V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.lean" \
  "$root_checked/FunsExternal.lean"

compact_compile_root=$(realpath "$replay_tmp/root-checked")
compact_olean_dir="$root_olean/V7CompactSemanticChallengeOpaqueNoDedup"
compact_types_olean="$compact_olean_dir/Types.olean"
compact_external_olean="$compact_olean_dir/FunsExternal.olean"
compact_funs_olean="$compact_olean_dir/Funs.olean"
for compact_input in Types FunsExternal Funs; do
  compact_input_real=$(realpath "$root_checked/$compact_input.lean")
  [[ "$compact_input_real" == "$compact_compile_root/"* ]]
done
for compact_output in \
  "$compact_types_olean" \
  "$compact_external_olean" \
  "$compact_funs_olean"; do
  [[ $(dirname "$compact_output") == "$compact_olean_dir" ]]
done
(
  cd "$compact_compile_root"
  export LEAN_PATH="$root_olean:$generated_olean:$formal_olean:$aeneas_lean_root/.lake/build/lib/lean:$aspis_lean_path"
  "$lean_bin" -o "$compact_types_olean" \
    V7CompactSemanticChallengeOpaqueNoDedup/Types.lean
  [[ -f "$compact_types_olean" ]]
  "$lean_bin" -o "$compact_external_olean" \
    V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.lean
  [[ -f "$compact_external_olean" ]]
  "$lean_bin" -o "$compact_funs_olean" \
    V7CompactSemanticChallengeOpaqueNoDedup/Funs.lean
  [[ -f "$compact_funs_olean" ]]
)

if rg -n '\b(sorry|admit|axiom|native_decide)\b' \
    "$script_dir/generated/V7Tag73ChallengeQm31" \
    "$script_dir/proof/V7Tag73ChallengeQm31SourceCertificate.lean" \
    "$formal_k1/V7Tag73SamplerDecoderExact.lean" \
    "$script_dir/replacement/V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.lean"; then
  echo 'forbidden proof escape found in checked sampler closure' >&2
  exit 1
fi

printf 'canonical LLBC sha256: %s\n' "$actual_llbc_sha"
echo 'V7 Tag-73 challenge_qm31 source replay: PASS'
