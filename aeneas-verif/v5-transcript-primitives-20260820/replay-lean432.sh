#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly checked_generated="$bundle/generated/V5TranscriptPrimitivesGenerated"
readonly proof="$bundle/proof/V5TranscriptPrimitivesProof.lean"
readonly sampler_semantics="$bundle/proof/V5QuerySamplerGeneratedSemantics.lean"
readonly fixed_sampler="$bundle/proof/V5QuerySamplerFixedCall.lean"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to patched Aeneas 000c7b6a}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/target/release/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/src/_build/default/main.exe}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean library directory}"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="000c7b6a4ab001ddceb16a82dd7fd37c3abfe24d"
readonly expected_transcript_blob="82cb1e4fc4316bff2b108263aa099303bd6c0e97"
readonly expected_manifest_blob="82ba74912115915aba5824f3421e0847c3ab499b"
readonly expected_lock_blob="d4294f30e81b1a93a6f075b07c94b5f50272a42c"
readonly expected_harness_blob="946d7e1539465536c0cd552e1fceaceab5be83d6"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/transcript.rs)" == \
  "$expected_transcript_blob" ]]
[[ "$(git -C "$root" hash-object aeneas-verif/v5-transcript-primitives-20260820/harness/Cargo.toml)" == \
  "$expected_manifest_blob" ]]
[[ "$(git -C "$root" hash-object aeneas-verif/v5-transcript-primitives-20260820/harness/Cargo.lock)" == \
  "$expected_lock_blob" ]]
[[ "$(git -C "$root" hash-object aeneas-verif/v5-transcript-primitives-20260820/harness/src/lib.rs)" == \
  "$expected_harness_blob" ]]

if [[ -n "${V5_TRANSCRIPT_REPLAY_OUT:-}" ]]; then
  out=$V5_TRANSCRIPT_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-transcript-primitives.XXXXXX)
fi
readonly out
readonly llbc="$out/all.llbc"
readonly raw_generated="$out/raw-generated"
readonly normalized_generated="$out/normalized/V5TranscriptPrimitivesGenerated"
readonly olean_out="$out/olean"
readonly log="$out/replay.log"
mkdir -p "$raw_generated" "$normalized_generated" \
  "$olean_out/V5TranscriptPrimitivesGenerated"
: > "$log"

echo "CHECK extraction harness" | tee -a "$log"
cargo check --release --locked --quiet --manifest-path "$harness/Cargo.toml" \
  >> "$log" 2>&1

echo "EXTRACT unchanged production transcript methods" | tee -a "$log"
CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
  --preset aeneas \
  --start-from 'v5_transcript_primitives_harness::extract_absorb' \
  --start-from 'v5_transcript_primitives_harness::extract_squeeze_block' \
  --start-from 'v5_transcript_primitives_harness::extract_queries_without_replacement' \
  --start-from 'v5_transcript_primitives_harness::extract_grinding_ok' \
  --include 'aspis_core::transcript' \
  --dest-file "$llbc" -- --manifest-path "$harness/Cargo.toml" --release --locked \
  >> "$log" 2>&1

echo "TRANSLATE production methods to Lean" | tee -a "$log"
"$aeneas_bin" -backend lean -split-files -dest "$raw_generated" \
  -print-error-emitters -abort-on-error -no-progress-bar "$llbc" \
  >> "$log" 2>&1

ROOT_PREFIX="$root/" perl -pe '
  if ($_ eq "import Aeneas\n") {
    $_ = "import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n";
  }
  s/import All\.Types/import V5TranscriptPrimitivesGenerated.Types/;
  s/import All\.FunsExternal/import V5TranscriptPrimitivesGenerated.FunsExternal/;
  s/namespace v5_transcript_primitives_harness/namespace V5TranscriptPrimitivesGenerated/g;
  s/end v5_transcript_primitives_harness/end V5TranscriptPrimitivesGenerated/g;
  s/\@\[discriminant isize, rust_type "aspis_core::transcript::QuerySampleError"\]/\@[rust_type "aspis_core::transcript::QuerySampleError"\]/;
  s/\Q$ENV{ROOT_PREFIX}\E//g;
' "$raw_generated/Types.lean" > "$normalized_generated/Types.lean"

ROOT_PREFIX="$root/" perl -pe '
  if ($_ eq "import Aeneas\n") {
    $_ = "import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n";
  }
  s/import All\.Types/import V5TranscriptPrimitivesGenerated.Types/;
  s/import All\.FunsExternal/import V5TranscriptPrimitivesGenerated.FunsExternal/;
  s/namespace v5_transcript_primitives_harness/namespace V5TranscriptPrimitivesGenerated/g;
  s/end v5_transcript_primitives_harness/end V5TranscriptPrimitivesGenerated/g;
  s/\Q$ENV{ROOT_PREFIX}\E//g;
' "$raw_generated/Funs.lean" > "$normalized_generated/Funs.lean"

cmp "$normalized_generated/Types.lean" "$checked_generated/Types.lean"
cmp "$normalized_generated/Funs.lean" "$checked_generated/Funs.lean"

echo "COMPILE generated code and bridge proofs" | tee -a "$log"
aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$olean_out:$aeneas_lib:$aspis_path"

"$lean_bin" -j 1 -o "$olean_out/V5TranscriptPrimitivesGenerated/Types.olean" \
  "$checked_generated/Types.lean" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5TranscriptPrimitivesGenerated/FunsExternal.olean" \
  "$checked_generated/FunsExternal.lean" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5TranscriptPrimitivesGenerated/Funs.olean" \
  "$checked_generated/Funs.lean" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5TranscriptPrimitivesProof.olean" \
  "$proof" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5QuerySamplerGeneratedSemantics.olean" \
  "$sampler_semantics" >> "$log" 2>&1
"$lean_bin" -j 1 -o "$olean_out/V5QuerySamplerFixedCall.olean" \
  "$fixed_sampler" >> "$log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_generated/Types.lean" "$checked_generated/Funs.lean" \
    "$checked_generated/FunsExternal.lean" "$proof" \
    "$sampler_semantics" "$fixed_sampler"; then
  echo "forbidden proof token or generated axiom" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof shortcut" >&2
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

echo "Lean 4.32 production transcript extraction: PASS"
echo "V5_TRANSCRIPT_REPLAY_OUT=$out"
echo "log: $log"
