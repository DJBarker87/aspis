#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly checked_generated="$bundle/generated/V5RelationKernels.lean"
readonly proof="$bundle/proof/V5PreparedPointClaimsProof.lean"
readonly lowering_proof="$bundle/proof/V5DeployedNestedLoopLoweringProof.lean"
readonly lowering_patch="$bundle/deployed-nested-loop-lowering.patch"
readonly decoder_proof="$bundle/proof/V5PreparedPointClaimsDecoderProof.lean"
readonly arithmetic_source="$root/aeneas-verif/component-b-weight-at/arithmetic-lean432"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean 4.32 library}"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_source_commit="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly expected_fri_checks_blob="3b1f37f2504aa2b309cad82605c88cab11afcb85"
readonly expected_lowered_fri_checks_blob="d7335af27eb4ad0817ca12603a8aac36a9a9125a"
readonly expected_lowering_patch_sha256="d6dae507133a366f1ebf0f22ee0f1e48fd02855418bc95be497795d85330a087"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_harness_manifest_blob="2b9472e979bbcc73f7306751de7b1675a5245e2b"
readonly expected_harness_source_blob="eac766f119033c0e3be10e91a45c3cab1eec9717"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/RustAttributes.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object programs/aspis-verifier/src/v5_fri_checks.rs)" == \
  "$expected_fri_checks_blob" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]
[[ "$(git -C "$root" hash-object \
  aeneas-verif/v5-relation-prepared-claims-20260815/harness/Cargo.toml)" == \
  "$expected_harness_manifest_blob" ]]
[[ "$(git -C "$root" hash-object \
  aeneas-verif/v5-relation-prepared-claims-20260815/harness/src/lib.rs)" == \
  "$expected_harness_source_blob" ]]

if [[ -n "${V5_PREPARED_CLAIMS_REPLAY_OUT:-}" ]]; then
  out=$V5_PREPARED_CLAIMS_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-prepared-claims.XXXXXX)
fi
readonly out
readonly log="$out/replay.log"
readonly llbc="$out/v5_relation_kernels.llbc"
readonly raw_generated="$out/raw-generated"
readonly normalized_generated="$out/normalized-generated"
readonly decoder_out="$out/decoder"
readonly arithmetic_out="$out/arithmetic"
readonly olean_out="$out/olean"
readonly bridge_lean_log="$out/bridge-lean.log"
readonly lowering_check="$out/lowering-check"
mkdir -p "$raw_generated" "$normalized_generated" "$decoder_out" \
  "$arithmetic_out" "$olean_out" \
  "$lowering_check/programs/aspis-verifier/src"
: > "$log"
: > "$bridge_lean_log"

echo "CHECK exact deployed-loop extraction patch" | tee -a "$log"
[[ "$(shasum -a 256 "$lowering_patch" | awk '{print $1}')" == \
  "$expected_lowering_patch_sha256" ]]
git -C "$root" show \
  "$expected_source_commit:programs/aspis-verifier/src/v5_fri_checks.rs" > \
  "$lowering_check/programs/aspis-verifier/src/v5_fri_checks.rs"
[[ "$(git hash-object \
  "$lowering_check/programs/aspis-verifier/src/v5_fri_checks.rs")" == \
  "$expected_fri_checks_blob" ]]
git apply --unsafe-paths --directory="$lowering_check" "$lowering_patch"
[[ "$(git hash-object \
  "$lowering_check/programs/aspis-verifier/src/v5_fri_checks.rs")" == \
  "$expected_lowered_fri_checks_blob" ]]

echo "EXTRACT production gamma and dot kernels" | tee -a "$log"
(
  cd "$harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'v5_relation_prepared_claims_harness::fri_checks::v5_gamma_powers' \
    --start-from \
      'v5_relation_prepared_claims_harness::fri_checks::v5_claim_dot_block' \
    --start-from \
      'v5_relation_prepared_claims_harness::extracted_qm31_add' \
    --include 'aspis_core::field' \
    --dest-file "$llbc" -- --release --locked
) >> "$log" 2>&1

echo "TRANSLATE extracted kernels" | tee -a "$log"
"$aeneas_bin" -backend lean \
  -namespace V5RelationPreparedClaimsGenerated \
  -dest "$raw_generated" \
  -max-heartbeats 800000 -max-recdepth 3000 \
  "$llbc" >> "$log" 2>&1

# Aeneas records an absolute source root in comments.  Remove only that root.
# The patched Lean 4.32 proof environment exposes the two imports used below
# rather than a monolithic `Aeneas.olean`; this does not alter definitions.
ROOT_PREFIX="$root/" perl -pe '
  if ($_ eq "import Aeneas\n") {
    $_ = "import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n";
  }
  s/\Q$ENV{ROOT_PREFIX}\E//g;
' "$raw_generated/V5RelationKernels.lean" > \
  "$normalized_generated/V5RelationKernels.lean"

cmp "$normalized_generated/V5RelationKernels.lean" "$checked_generated"

echo "BUILD maintained point-claim model" | tee -a "$log"
(
  cd "$root/AspisFormal"
  lake build AspisFormal.V5PreparedPointClaimsSourceBridge
) >> "$log" 2>&1

echo "REPLAY extracted byte-decoder equality" | tee -a "$log"
LEAN432_BIN="$lean_bin" AENEAS_LEAN_LIB="$aeneas_lib" \
  V5_FRI_DECODER_REPLAY_OUT="$decoder_out" \
  "$root/aeneas-verif/v5-fri-byte-decoders-20260814/replay-lean432.sh" \
  >> "$log" 2>&1

aspis_path=$(cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)

echo "COMPILE byte-decoder bridge in its extraction namespace" | tee -a "$log"
LEAN_PATH="$decoder_out:$aspis_path:$aeneas_lib" \
  "$lean_bin" -R "$root" -j 1 \
  -o "$decoder_out/V5PreparedPointClaimsDecoderProof.olean" \
  "$decoder_proof" >> "$bridge_lean_log" 2>&1

echo "COMPILE reused source-authentic field arithmetic proofs" | tee -a "$log"
export LEAN_PATH="$arithmetic_out:$arithmetic_source:$aspis_path:$aeneas_lib"
for module in \
  AspisCoreFieldReduceU64 \
  M31ReduceU64Proof \
  AspisCoreFieldMulNamespaced \
  M31MulProof \
  CM31ExactModel \
  AspisCoreCm31Multiplicative \
  CM31MultiplicativeProof \
  QM31MulProof \
  AspisCoreQm31SquareScalars \
  QM31SquareScalarsProof
do
  "$lean_bin" -R "$arithmetic_source" -j 1 \
    -o "$arithmetic_out/$module.olean" \
    "$arithmetic_source/$module.lean" >> "$bridge_lean_log" 2>&1
done

echo "COMPILE regenerated kernels and universal bridge" | tee -a "$log"
export LEAN_PATH="$olean_out:$aspis_path:$aeneas_lib"
"$lean_bin" -R "$normalized_generated" -j 1 \
  -o "$olean_out/V5RelationKernels.olean" \
  "$normalized_generated/V5RelationKernels.lean" >> "$bridge_lean_log" 2>&1
export LEAN_PATH="$arithmetic_out:$olean_out:$arithmetic_source:$aspis_path:$aeneas_lib"
"$lean_bin" -R "$root" -j 1 \
  -o "$olean_out/V5PreparedPointClaimsProof.olean" \
  "$proof" >> "$bridge_lean_log" 2>&1
"$lean_bin" -R "$root" -j 1 \
  -o "$olean_out/V5DeployedNestedLoopLoweringProof.olean" \
  "$lowering_proof" >> "$bridge_lean_log" 2>&1
cat "$bridge_lean_log" >> "$log"

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_generated" "$proof" "$lowering_proof" \
    "$decoder_proof" \
    "$root/AspisFormal/AspisFormal/V5PreparedPointClaimsSourceBridge.lean"; then
  echo "forbidden proof token or generated axiom" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$bridge_lean_log"; then
  echo "forbidden axiom in prepared-claim bridge" >&2
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
' "$bridge_lean_log"; then
  exit 1
fi

echo "Lean 4.32 V5 prepared-claim decoder and kernel bridges: PASS"
echo "V5_PREPARED_CLAIMS_REPLAY_OUT=$out"
echo "log: $log"
