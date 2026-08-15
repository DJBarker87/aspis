#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly checked_generated="$bundle/generated/V5NonzeroKappa"
readonly generated_proof="$bundle/proof/V5NonzeroKappaGeneratedProof.lean"
readonly formal_proof="$root/AspisFormal/AspisFormal/V5NonzeroKappaSourceBridge.lean"

readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly aeneas_lean_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Lean-4.32 Aeneas library directory}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_transcript_blob="82cb1e4fc4316bff2b108263aa099303bd6c0e97"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_verifier_blob="ca28d560e44e5e82e689321f32289831c889a0bd"
readonly expected_harness_toml_blob="cba86648cd665c313725ab1250b993cae9420eb1"
readonly expected_harness_lock_blob="168133990b870f5b24ce4e08bc1fe8cdb12e0e27"
readonly expected_types_semantic_sha256="ce63ce26ab929699f82631469cc0faa6c60d6169bc178f811502d7d696abd288"
readonly expected_funs_semantic_sha256="0f0f5c081ebb8f22a3e7fbc213f18c4c58e2bcfe539bb3a7d790232d36da1df5"

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

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lean_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/transcript.rs)" == \
  "$expected_transcript_blob" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_cu_probe.rs)" == \
  "$expected_verifier_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.toml")" == \
  "$expected_harness_toml_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.lock")" == \
  "$expected_harness_lock_blob" ]]

if [[ -n "${V5_NONZERO_KAPPA_REPLAY_OUT:-}" ]]; then
  out=$V5_NONZERO_KAPPA_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-nonzero-kappa.XXXXXX)
fi
readonly out
readonly llbc="$out/V5NonzeroKappa.llbc"
readonly full_llbc="$out/V5NonzeroKappaFull.llbc"
readonly raw="$out/raw"
readonly full_raw="$out/full-raw"
readonly extract_log="$out/extract.log"
readonly aeneas_log="$out/aeneas.log"
readonly full_aeneas_log="$out/aeneas-inner-sampler-boundary.log"
readonly lean_log="$out/lean432.log"
readonly olean_root="$out/olean"
mkdir -p "$raw" "$full_raw" "$olean_root/V5NonzeroKappa"
: > "$extract_log"
: > "$aeneas_log"
: > "$full_aeneas_log"
: > "$lean_log"

echo "EXTRACT exact production three-attempt nonzero wrapper" | tee -a "$extract_log"
(
  cd "$harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'aspis_core_nonzero_kappa_extraction::transcript::_::challenge_nonzero_qm31' \
    --opaque 'aspis_core_nonzero_kappa_extraction::transcript::Transcript' \
    --opaque \
      'aspis_core_nonzero_kappa_extraction::transcript::_::challenge_qm31' \
    --dest-file "$llbc" -- --locked
) >> "$extract_log" 2>&1

"$charon_bin" pretty-print "$llbc" > "$out/nonzero-wrapper.llbc.txt"
rg -F 'challenge_nonzero_qm31' "$out/nonzero-wrapper.llbc.txt" >/dev/null
rg -F 'NONZERO_QM31_RETRY_LIMIT' "$out/nonzero-wrapper.llbc.txt" >/dev/null
rg -F 'challenge_qm31' "$out/nonzero-wrapper.llbc.txt" >/dev/null

"$aeneas_bin" -backend lean -namespace V5NonzeroKappaGenerated \
  -split-files -no-progress-bar \
  -dest "$raw" "$llbc" > "$aeneas_log" 2>&1

# Aeneas emits comments containing local absolute source locations and imports
# its full compatibility module.  The checked copies use the narrower Lean-4.32
# imports.  Compare the executable declarations after those two mechanical
# normalizations; no definition or theorem body is ignored.
normalize_types() {
  perl -0777 -pe \
    's/import Aeneas\n/import Aeneas.Std\n/; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

normalize_funs() {
  perl -0777 -pe \
    's/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n/; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

normalize_types "$raw/Types.lean" > "$out/raw.Types.semantic"
normalize_types "$checked_generated/Types.lean" > "$out/checked.Types.semantic"
normalize_funs "$raw/Funs.lean" > "$out/raw.Funs.semantic"
normalize_funs "$checked_generated/Funs.lean" > "$out/checked.Funs.semantic"

cmp "$out/raw.Types.semantic" "$out/checked.Types.semantic"
cmp "$out/raw.Funs.semantic" "$out/checked.Funs.semantic"
[[ "$(shasum -a 256 "$out/raw.Types.semantic" | awk '{print $1}')" == \
  "$expected_types_semantic_sha256" ]]
[[ "$(shasum -a 256 "$out/raw.Funs.semantic" | awk '{print $1}')" == \
  "$expected_funs_semantic_sha256" ]]

# Also try the stronger extraction that includes the lower hash-to-field
# sampler.  Pinned Aeneas currently stops at that inner source loop.  Requiring
# the precise failure prevents this replay from silently claiming that the
# arbitrary-result adapter proves SHA-256 sampling or uniformity.
echo "EXTRACT wrapper plus production inner field sampler" | tee -a "$extract_log"
(
  cd "$harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'aspis_core_nonzero_kappa_extraction::transcript::_::challenge_nonzero_qm31' \
    --opaque 'aspis_core_nonzero_kappa_extraction::transcript::Transcript' \
    --dest-file "$full_llbc" -- --locked
) >> "$extract_log" 2>&1

if "$aeneas_bin" -backend lean -namespace V5NonzeroKappaGenerated \
    -split-files -no-progress-bar \
    -dest "$full_raw" "$full_llbc" > "$full_aeneas_log" 2>&1; then
  echo "pinned Aeneas unexpectedly translated the complete inner sampler" >&2
  exit 1
fi
rg -F 'Could not match the contexts' "$full_aeneas_log" >/dev/null
rg -F "lines 313:12-330:13" "$full_aeneas_log" >/dev/null
rg -F "challenge_qm31" "$full_aeneas_log" >/dev/null

# The whole verifier source is blob-pinned above.  These checks identify the
# exact source assignments which move the sampled value into the verified
# prefix and then into relation batching with powers 1, kappa, kappa^2,
# kappa^3.  The universal proof of this large caller remains separately named
# in V5NonzeroKappaSourceBridge.lean.
readonly verifier="$root/programs/aspis-verifier/src/v5_cu_probe.rs"
rg -F 'let kappa = transcript' "$verifier" >/dev/null
rg -F '.challenge_nonzero_qm31()' "$verifier" >/dev/null
rg -F 'decode_qm31(parsed.relation_scales, 1)? != kappa' "$verifier" >/dev/null
rg -F 'let kappa = verified_prefix.kappa;' "$verifier" >/dev/null
rg -F 'let point_scales = [QM31::ONE, kappa, kappa2];' "$verifier" >/dev/null
rg -F 'let kappa3 = kappa2.mul(kappa);' "$verifier" >/dev/null
rg -F 'relation_value = relation_value.add(kappa3.mul(dense_claim));' "$verifier" >/dev/null
rg -F 'prepare_relation_base_with_kappa_prepared(' "$verifier" >/dev/null

aspis_path=${ASPIS_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$olean_root:$bundle/generated:$aeneas_lean_lib:$aspis_path"

"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5NonzeroKappa/TypesExternal.olean" \
  "$checked_generated/TypesExternal.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5NonzeroKappa/Types.olean" \
  "$checked_generated/Types.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5NonzeroKappa/FunsExternal.olean" \
  "$checked_generated/FunsExternal.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5NonzeroKappa/Funs.olean" \
  "$checked_generated/Funs.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 -o "$out/V5NonzeroKappaGeneratedProof.olean" \
  "$generated_proof" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 -o "$out/V5NonzeroKappaSourceBridge.olean" \
  "$formal_proof" >> "$lean_log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_generated" "$generated_proof" "$formal_proof"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$lean_log"; then
  echo "forbidden axiom in nonzero batching-challenge proof" >&2
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

echo "Exact production three-attempt wrapper and generated-code proofs: PASS"
echo "Nonzero collision count and 3/(QM31-1) <= 2^-122: PASS"
echo "Maintained relation formula uses 1, kappa, kappa^2, kappa^3: PASS"
echo "Inner hash-derived uniform sampling: ASSUMPTION"
echo "Exact relation-phase kappa forwarding: SEE replay-relation-caller-lean432.sh"
echo "Prefix-output kappa to relation-phase input: OPEN translator boundary"
echo "V5_NONZERO_KAPPA_REPLAY_OUT=$out"
echo "extraction log: $extract_log"
echo "Aeneas boundary log: $full_aeneas_log"
echo "Lean log: $lean_log"
