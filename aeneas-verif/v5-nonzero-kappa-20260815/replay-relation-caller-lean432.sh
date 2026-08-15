#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/relation-harness"
readonly checked_generated="$bundle/generated/V5KappaRelationCaller"
readonly generated_proof="$bundle/proof/V5KappaRelationCallerGeneratedProof.lean"

readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly aeneas_lean_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Lean-4.32 Aeneas library directory}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_verifier_blob="ca28d560e44e5e82e689321f32289831c889a0bd"
readonly expected_relation_stress_blob="cbe62500353df776318fcb8933bc1c2200097ade"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_harness_toml_blob="e2a5b6412e9410ffd1e392d8ea32033aab76f83f"
readonly expected_harness_lock_blob="728dc91c3f1f9d6443df8b793c617b340a2e2a45"
readonly expected_solana_toml_sha256="d77304602d544d2c23567e22f5940bee52ce7f6803eb538072d7c41f662a3d07"
readonly expected_solana_program_sha256="5b99eb5fd85023f6a3239e7fe7dd40f279ae2f9d08ec47b465268cdcf21a9108"
readonly expected_types_semantic_sha256="954864f46a836395c5d75e21cc308928e00c860b2df16c62733faf1f03d51a8c"
readonly expected_funs_semantic_sha256="ff98c980b528d74b8b367620fa7ef8d09f78058b5578a977cdeaf5e00c4d1297"

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
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_cu_probe.rs)" == \
  "$expected_verifier_blob" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_relation_stress.rs)" == \
  "$expected_relation_stress_blob" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.toml")" == \
  "$expected_harness_toml_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.lock")" == \
  "$expected_harness_lock_blob" ]]

if [[ -n "${V5_KAPPA_RELATION_REPLAY_OUT:-}" ]]; then
  out=$V5_KAPPA_RELATION_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-kappa-relation.XXXXXX)
fi
readonly out
readonly vendor="$out/vendor"
readonly replay_harness="$out/harness"
readonly llbc="$out/V5KappaRelationCaller.llbc"
readonly composite_llbc="$out/V5KappaCompositeCaller.llbc"
readonly raw="$out/raw"
readonly composite_raw="$out/composite-raw"
readonly extract_log="$out/extract.log"
readonly aeneas_log="$out/aeneas.log"
readonly composite_log="$out/composite-aeneas-boundary.log"
readonly lean_log="$out/lean432.log"
readonly olean_root="$out/olean"
mkdir -p "$vendor" "$replay_harness" "$raw" "$composite_raw" \
  "$olean_root/V5KappaRelationCaller"
: > "$extract_log"
: > "$aeneas_log"
: > "$composite_log"
: > "$lean_log"

# Pinned Charon's compiler tries every declared crate type of dependencies.
# Solana 2.3.0 declares a host cdylib that cannot link on this toolchain, and
# one test-only expression trips the pinned compiler's implicit-autoref rule.
# Patch a temporary vendored copy only; neither edit changes the target caller.
(
  cd "$harness"
  cargo vendor --locked "$vendor" > "$out/vendor-config.toml" 2>> "$extract_log"
)
readonly solana_program="$vendor/solana-program"
[[ "$(shasum -a 256 "$solana_program/Cargo.toml" | awk '{print $1}')" == \
  "$expected_solana_toml_sha256" ]]
[[ "$(shasum -a 256 "$solana_program/src/program.rs" | awk '{print $1}')" == \
  "$expected_solana_program_sha256" ]]
[[ "$(rg -Fxc '    "cdylib",' "$solana_program/Cargo.toml")" == 1 ]]
rg -F 'assert_eq!((*(*data_ptr).as_ptr())[..], data[..]);' \
  "$solana_program/src/program.rs" >/dev/null
perl -pi -e 's/^    "cdylib",\n//' "$solana_program/Cargo.toml"
perl -pi -e \
  's/\Qassert_eq!((*(*data_ptr).as_ptr())[..], data[..]);\E/assert_eq!((&(*(*data_ptr).as_ptr()))[..], data[..]);/' \
  "$solana_program/src/program.rs"
! rg -F '    "cdylib",' "$solana_program/Cargo.toml" >/dev/null
rg -F 'assert_eq!((&(*(*data_ptr).as_ptr()))[..], data[..]);' \
  "$solana_program/src/program.rs" >/dev/null

cp "$harness/Cargo.toml" "$harness/Cargo.lock" "$replay_harness/"
perl -pi -e "s#\.\./\.\./\.\./programs#$root/programs#g; \
  s#\.\./\.\./\.\./crates#$root/crates#g" "$replay_harness/Cargo.toml"

echo "EXTRACT exact production relation-phase caller" | tee -a "$extract_log"
(
  cd "$replay_harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_mode9_relation_phase' \
    --opaque 'aspis_verifier_kappa_caller_extraction::v5_cu_probe' \
    --include \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_mode9_relation_phase' \
    --include \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::ParsedProbeData' \
    --include \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::PreparedRelation' \
    --include \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::RelationVariant' \
    --opaque 'aspis_verifier_kappa_caller_extraction::v5_relation_stress' \
    --include \
      'aspis_verifier_kappa_caller_extraction::v5_relation_stress::VerifiedV5RelationStress' \
    --include \
      'aspis_verifier_kappa_caller_extraction::v5_relation_stress::V5RelationStressError' \
    --opaque 'core::cmp' \
    --exclude 'core::iter' \
    --exclude 'core::slice::iter' \
    --dest-file "$llbc" -- --offline \
      --config "patch.crates-io.solana-program.path=\"$solana_program\""
) >> "$extract_log" 2>&1

"$charon_bin" pretty-print "$llbc" > "$out/relation-caller.llbc.txt"
rg -F 'verify_mode9_relation_phase' "$out/relation-caller.llbc.txt" >/dev/null
rg -F 'prepare_relation_base_with_kappa_prepared' \
  "$out/relation-caller.llbc.txt" >/dev/null
rg -F 'RelationVariant::FourClaimsCompact' \
  "$out/relation-caller.llbc.txt" >/dev/null

"$aeneas_bin" -backend lean \
  -namespace V5KappaRelationCallerGenerated \
  -split-files -no-progress-bar \
  -dest "$raw" "$llbc" > "$aeneas_log" 2>&1

# Compare every executable generated declaration. Local source paths, comments,
# imports, and whitespace are the only normalized text.
normalize_generated() {
  perl -0777 -pe \
    's/^import[^\n]*\n//mg; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

normalize_generated "$raw/Types.lean" > "$out/raw.Types.semantic"
normalize_generated "$checked_generated/Types.lean" > \
  "$out/checked.Types.semantic"
normalize_generated "$raw/Funs.lean" > "$out/raw.Funs.semantic"
normalize_generated "$checked_generated/Funs.lean" > \
  "$out/checked.Funs.semantic"
cmp "$out/raw.Types.semantic" "$out/checked.Types.semantic"
cmp "$out/raw.Funs.semantic" "$out/checked.Funs.semantic"
[[ "$(shasum -a 256 "$out/raw.Types.semantic" | awk '{print $1}')" == \
  "$expected_types_semantic_sha256" ]]
[[ "$(shasum -a 256 "$out/raw.Funs.semantic" | awk '{print $1}')" == \
  "$expected_funs_semantic_sha256" ]]

# Attempt the next larger caller as well. Its opaque prefix verifier exposes
# HashFn = fn(&[&[u8]]) -> [u8; 32], whose locally quantified reference regions
# are unsupported by this pinned Aeneas. Requiring the exact failure keeps the
# remaining prefix-output-to-relation-input link explicit.
echo "EXTRACT larger composite caller to record translator boundary" | \
  tee -a "$extract_log"
(
  cd "$replay_harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_mode9_composite_with_live_statement' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_v5_wire_prefix' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_mode9_atomic_terminal_with_prefix' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::replay_real_v5_relation_rounds' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::derive_v5_selected_good_queries_from_transcript' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::decode_v5_fri_alphas' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_mode9_fri_phase' \
    --opaque \
      'aspis_verifier_kappa_caller_extraction::v5_cu_probe::verify_mode9_relation_phase' \
    --dest-file "$composite_llbc" -- --offline \
      --config "patch.crates-io.solana-program.path=\"$solana_program\""
) >> "$extract_log" 2>&1

if "$aeneas_bin" -backend lean \
    -namespace V5KappaCompositeCallerGenerated \
    -split-files -no-progress-bar \
    -dest "$composite_raw" "$composite_llbc" > "$composite_log" 2>&1; then
  echo "pinned Aeneas unexpectedly translated the complete composite caller" >&2
  exit 1
fi
rg -F "We don't support arrow types with locally quantified regions" \
  "$composite_log" >/dev/null
rg -F 'verify_v5_wire_prefix' "$composite_log" >/dev/null
rg -F 'verify_mode9_composite_with_live_statement' "$composite_log" >/dev/null

aspis_path=${ASPIS_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$olean_root:$bundle/generated:$aeneas_lean_lib:$aspis_path"

"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5KappaRelationCaller/TypesExternal.olean" \
  "$checked_generated/TypesExternal.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5KappaRelationCaller/Types.olean" \
  "$checked_generated/Types.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5KappaRelationCaller/FunsExternal.olean" \
  "$checked_generated/FunsExternal.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 \
  -o "$olean_root/V5KappaRelationCaller/Funs.olean" \
  "$checked_generated/Funs.lean" >> "$lean_log" 2>&1
"${lean_cmd[@]}" -j 1 -o "$out/V5KappaRelationCallerGeneratedProof.olean" \
  "$generated_proof" >> "$lean_log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_generated" "$generated_proof"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$lean_log"; then
  echo "forbidden axiom in relation caller proof" >&2
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

echo "Exact production relation-phase Aeneas translation: PASS"
echo "FourClaimsCompact and unchanged kappa forwarding: PASS"
echo "Opaque downstream-call observation proof: PASS"
echo "Prefix-output kappa to relation-phase input: TRANSLATOR BOUNDARY"
echo "V5_KAPPA_RELATION_REPLAY_OUT=$out"
echo "extraction log: $extract_log"
echo "Aeneas boundary log: $composite_log"
echo "Lean log: $lean_log"
