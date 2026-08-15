#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly proof="$root/AspisFormal/AspisFormal/V5QuerySamplerControl.lean"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_transcript_blob="82cb1e4fc4316bff2b108263aa099303bd6c0e97"
readonly expected_source_excerpt_sha256="a04a6041502f6a9c3e75ad484a00226de858b2519a63f065610cbcd8d225bc47"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/transcript.rs)" == \
  "$expected_transcript_blob" ]]

actual_source_excerpt_sha256=$(
  sed -n '429,468p' "$root/crates/aspis-core/src/transcript.rs" |
    shasum -a 256 | awk '{print $1}'
)
[[ "$actual_source_excerpt_sha256" == "$expected_source_excerpt_sha256" ]]

if [[ -n "${V5_QUERY_SAMPLER_REPLAY_OUT:-}" ]]; then
  out=$V5_QUERY_SAMPLER_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-query-sampler-control.XXXXXX)
fi
readonly out
readonly llbc="$out/query_sampler.llbc"
readonly generated="$out/generated"
readonly extract_log="$out/extract.log"
readonly aeneas_log="$out/aeneas-known-boundary.log"
readonly lean_log="$out/lean432.log"
readonly olean="$out/V5QuerySamplerControl.olean"
mkdir -p "$generated"
: > "$extract_log"
: > "$aeneas_log"
: > "$lean_log"

echo "EXTRACT exact production sampler" | tee -a "$extract_log"
(
  cd "$harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'aspis_core_query_sampler_extraction::transcript::_::challenge_queries_without_replacement' \
    --opaque 'aspis_core_query_sampler_extraction::transcript::Transcript' \
    --opaque 'aspis_core_query_sampler_extraction::transcript::_::squeeze_block' \
    --dest-file "$llbc" -- --locked
) >> "$extract_log" 2>&1

"$charon_bin" pretty-print "$llbc" > "$out/query-sampler.llbc.txt"
rg -F 'challenge_queries_without_replacement' "$out/query-sampler.llbc.txt" >/dev/null
rg -F 'continue 1' "$out/query-sampler.llbc.txt" >/dev/null
rg -F 'candidate = move _' "$out/query-sampler.llbc.txt" >/dev/null
rg -F '& move _' "$out/query-sampler.llbc.txt" >/dev/null

# Pinned Aeneas rejects the source-authentic nested-loop continuation before
# emitting a function definition.  Require that precise boundary so a replay
# cannot silently turn the pure model below into a claimed Rust translation.
if "$aeneas_bin" -backend lean -split-files -no-progress-bar \
    -dest "$generated" "$llbc" > "$aeneas_log" 2>&1; then
  echo "pinned Aeneas unexpectedly reported a complete translation" >&2
  exit 1
fi
rg -F 'Continues to outer loops not supported yet' "$aeneas_log" >/dev/null
rg -F "Could not translate the body of function" "$aeneas_log" >/dev/null

aspis_path=${ASPIS_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$out:$aspis_path"
"$lean_bin" -j 1 -o "$olean" "$proof" > "$lean_log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' "$proof"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$lean_log"; then
  echo "forbidden axiom in query-sampler control proof" >&2
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
' "$lean_log"; then
  exit 1
fi

echo "Production sampler extraction and Lean control model: PASS"
echo "Universal Rust-to-Lean sampler equality: OPEN (pinned Aeneas outer-continue limitation)"
echo "V5_QUERY_SAMPLER_REPLAY_OUT=$out"
echo "extraction log: $extract_log"
echo "Lean log: $lean_log"
