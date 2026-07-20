#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly AENEAS_URL="https://github.com/AeneasVerif/aeneas.git"
readonly MATHLIB_TAG="v4.32.0"
readonly MATHLIB_COMMIT="81a5d257c8e410db227a6665ed08f64fea08e997"
readonly LEAN_VERSION="4.32.0"
readonly LEAN_COMMIT="8c9756b28d64dab099da31a4c09229a9e6a2ef35"
readonly PATCH_SHA256="04e9c2cf33d941b8e8959c9bc4b27607164e69a5d182377d8708b59f9eca2dc4"
readonly LAKE_MANIFEST_SHA256="5d15524cf34ff705bebbd037e80baec63683d5d5a3a37a539a62f17405a2fc62"
readonly SOURCE_HASHES_SHA256="a030daa0cf90263783dbedfe4809a11e9ee409a7a332e06c9e418941eb75509e"
readonly NORMALIZED_HASHES_SHA256="0a7cdedfa6264f5248da8117384da055150e7db5c6acaa6dfeca7de097c1a0fe"
readonly PATCHED_AENEAS_HASHES_SHA256="ef18cff71157c665bb92040c261d1a8543a5dfadffa74583ed81b963be4a804b"
readonly STAGED_HASHES_SHA256="0f8378c55c72645d9c15194f3cd641d716ac52e381785689722a9b8853044654"
readonly FIELD_SOURCE_BLOB="96e8c04efee6a8231adb2723dac9acf975993e06"
readonly FIELD_SOURCE_SHA256="b424ea2c70902e477a2580d683279645b3dd0423bfa1c9043494bc6a99dfad1e"

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd -P)"
readonly harness_dir="$verification_dir/lean432"
readonly proof_dir="$verification_dir/proof"
readonly live_patch_file="$harness_dir/aeneas-b59d5188-lean432.patch"
readonly live_lake_manifest="$harness_dir/lake-manifest.json"
readonly live_source_hashes="$harness_dir/source-hashes.sha256"
readonly live_normalized_hashes="$harness_dir/normalized-hashes.sha256"
readonly live_patched_aeneas_hashes="$harness_dir/patched-aeneas-hashes.sha256"
readonly live_staged_hashes="$harness_dir/staged-hashes.sha256"
readonly live_field_source="$workspace_dir/crates/aspis-core/src/field.rs"

readonly modules=(
  AspisCoreFieldReduceU64
  M31ReduceU64Proof
  AspisCoreFieldMulNamespaced
  M31MulProof
  CM31ExactModel
  AspisCoreCm31Multiplicative
  CM31MultiplicativeProof
  CM31SquareProof
  CM31MulM31Proof
  AspisCoreM31Inverse
  M31InverseProof
)

for command_name in git jq lake lean perl rg shasum; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 2
  fi
done

for required_file in \
    "$live_patch_file" \
    "$live_lake_manifest" \
    "$live_source_hashes" \
    "$live_normalized_hashes" \
    "$live_patched_aeneas_hashes" \
    "$live_staged_hashes" \
    "$live_field_source"; do
  if [[ ! -f "$required_file" ]]; then
    echo "missing Lean-4.32 harness file: $required_file" >&2
    exit 2
  fi
done

unset LEAN_PATH
unset LEAN_SRC_PATH

readonly work_dir="$(mktemp -d /private/tmp/aspis-aeneas-lean432-check.XXXXXX)"
readonly aeneas_checkout="$work_dir/aeneas"
readonly lean_backend="$aeneas_checkout/backends/lean"
readonly snapshot_dir="$work_dir/gate-inputs"
readonly snapshot_proof="$snapshot_dir/proof"
readonly patch_file="$snapshot_dir/aeneas-b59d5188-lean432.patch"
readonly pinned_lake_manifest="$snapshot_dir/lake-manifest.json"
readonly source_hashes="$snapshot_dir/source-hashes.sha256"
readonly normalized_hashes="$snapshot_dir/normalized-hashes.sha256"
readonly patched_aeneas_hashes="$snapshot_dir/patched-aeneas-hashes.sha256"
readonly staged_hashes="$snapshot_dir/staged-hashes.sha256"
readonly field_source_snapshot="$snapshot_dir/field.rs"
readonly staged_proof="$work_dir/staged-proof"
readonly olean_dir="$work_dir/olean"
readonly axiom_log="$work_dir/axioms.log"
readonly build_log="$work_dir/aeneas-std-build.log"

cleanup() {
  if [[ "${ASPIS_KEEP_LEAN432_WORK:-0}" == "1" ]]; then
    echo "LEAN432_WORK_DIR=$work_dir"
  else
    rm -rf "$work_dir"
  fi
}
trap cleanup EXIT

if [[ -n "${ASPIS_LEAN432_PATH_FILE:-}" ]] &&
    [[ "${ASPIS_KEEP_LEAN432_WORK:-0}" != "1" ]]; then
  echo "ASPIS_LEAN432_PATH_FILE requires ASPIS_KEEP_LEAN432_WORK=1" >&2
  exit 2
fi
if [[ -n "${ASPIS_LEAN432_PATH_FILE:-}" ]]; then
  printf '%s\n' "$work_dir" > "$ASPIS_LEAN432_PATH_FILE"
fi

sha256_of() {
  shasum -a 256 "$1" | awk '{print $1}'
}

require_sha256() {
  local expected="$1"
  local file="$2"
  local label="$3"
  local actual
  actual="$(sha256_of "$file")"
  if [[ "$actual" != "$expected" ]]; then
    echo "$label SHA-256 mismatch: expected $expected, got $actual" >&2
    exit 1
  fi
}

authenticate_snapshot() {
  require_sha256 "$PATCH_SHA256" "$patch_file" "Lean-4.32 compatibility patch"
  require_sha256 "$LAKE_MANIFEST_SHA256" "$pinned_lake_manifest" "Lean-4.32 Lake manifest"
  require_sha256 "$SOURCE_HASHES_SHA256" "$source_hashes" "raw-source hash manifest"
  require_sha256 "$NORMALIZED_HASHES_SHA256" "$normalized_hashes" "normalized-source hash manifest"
  require_sha256 "$PATCHED_AENEAS_HASHES_SHA256" "$patched_aeneas_hashes" "patched-Aeneas hash manifest"
  require_sha256 "$STAGED_HASHES_SHA256" "$staged_hashes" "final-staged hash manifest"

  if [[ "$(git hash-object "$field_source_snapshot")" != "$FIELD_SOURCE_BLOB" ]]; then
    echo "snapshotted field.rs is not the source blob authenticated by the extracted modules" >&2
    exit 1
  fi
  require_sha256 "$FIELD_SOURCE_SHA256" "$field_source_snapshot" "snapshotted field.rs"

  # Paths in this manifest are relative to the immutable gate-input snapshot.
  (
    cd "$snapshot_dir"
    shasum -a 256 -c "$(basename "$source_hashes")"
  )
}

mkdir -p "$snapshot_proof"
cp "$live_patch_file" "$patch_file"
cp "$live_lake_manifest" "$pinned_lake_manifest"
cp "$live_source_hashes" "$source_hashes"
cp "$live_normalized_hashes" "$normalized_hashes"
cp "$live_patched_aeneas_hashes" "$patched_aeneas_hashes"
cp "$live_staged_hashes" "$staged_hashes"
cp "$live_field_source" "$field_source_snapshot"
for module_name in "${modules[@]}"; do
  cp "$proof_dir/$module_name.lean" "$snapshot_proof/$module_name.lean"
done

# Freeze and authenticate every gate input before the potentially slow clone
# or dependency build.  All subsequent proof work reads only this snapshot.
authenticate_snapshot

readonly source_repo="${ASPIS_AENEAS_432_SOURCE:-$AENEAS_URL}"
git clone --quiet --no-local --no-checkout "$source_repo" "$aeneas_checkout"
git -C "$aeneas_checkout" checkout --quiet --detach "$AENEAS_COMMIT"

if [[ "$(git -C "$aeneas_checkout" rev-parse HEAD)" != "$AENEAS_COMMIT" ]]; then
  echo "Aeneas checkout is not the exact audited commit" >&2
  exit 1
fi
if [[ -n "$(git -C "$aeneas_checkout" status --short)" ]]; then
  echo "fresh Aeneas checkout is unexpectedly dirty" >&2
  exit 1
fi

git -C "$aeneas_checkout" apply --check --unidiff-zero "$patch_file"
git -C "$aeneas_checkout" apply --unidiff-zero "$patch_file"
git -C "$aeneas_checkout" diff --check

readonly expected_patch_files=$'backends/lean/Aeneas/Tactic/Simproc/ReduceZMod/ReduceZMod.lean\nbackends/lean/AeneasMeta/BvEnumToBitVec.lean\nbackends/lean/AeneasMeta/Simp/Simp.lean\nbackends/lean/lakefile.lean\nbackends/lean/lean-toolchain'
readonly actual_patch_files="$(git -C "$aeneas_checkout" diff --name-only | LC_ALL=C sort)"
if [[ "$actual_patch_files" != "$expected_patch_files" ]]; then
  echo "Lean-4.32 patch changed an unexpected Aeneas file" >&2
  printf '%s\n' "$actual_patch_files" >&2
  exit 1
fi
(
  cd "$aeneas_checkout"
  shasum -a 256 -c "$patched_aeneas_hashes"
)
cp "$pinned_lake_manifest" "$lean_backend/lake-manifest.json"
cp "$pinned_lake_manifest" "$work_dir/lake-manifest.before.json"

mkdir -p "$staged_proof" "$olean_dir"
for module_name in "${modules[@]}"; do
  cp "$snapshot_proof/$module_name.lean" "$staged_proof/$module_name.lean"
done

normalize_generated_import() {
  local module_name="$1"
  local add_rust_attributes="$2"
  local original="$snapshot_proof/$module_name.lean"
  local staged="$staged_proof/$module_name.lean"
  local roundtrip="$work_dir/$module_name.roundtrip.lean"

  if [[ "$(sed -n '3p' "$staged")" != "import Aeneas" ]] ||
      [[ "$(grep -c '^import Aeneas$' "$staged")" -ne 1 ]]; then
    echo "$module_name does not have the authenticated generated preamble" >&2
    exit 1
  fi

  if [[ "$add_rust_attributes" == "yes" ]]; then
    perl -0pi -e \
      's/^import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n/m' \
      "$staged"
    cp "$staged" "$roundtrip"
    perl -0pi -e \
      's/^import Aeneas\.Std\nimport Aeneas\.Tactic\.RustAttributes\n/import Aeneas\n/m' \
      "$roundtrip"
  else
    perl -0pi -e 's/^import Aeneas\n/import Aeneas.Std\n/m' "$staged"
    cp "$staged" "$roundtrip"
    perl -0pi -e 's/^import Aeneas\.Std\n/import Aeneas\n/m' "$roundtrip"
  fi

  # This round trip proves byte-for-byte that normalization touched only the
  # declared preamble.  It is stronger than comparing proof bodies by line.
  cmp "$original" "$roundtrip"
  local original_lines
  local staged_lines
  original_lines="$(wc -l < "$original" | tr -d ' ')"
  staged_lines="$(wc -l < "$staged" | tr -d ' ')"
  if [[ "$add_rust_attributes" == "yes" ]]; then
    if [[ "$staged_lines" -ne $((original_lines + 1)) ]]; then
      echo "$module_name normalization changed the wrong number of lines" >&2
      exit 1
    fi
  elif [[ "$staged_lines" -ne "$original_lines" ]]; then
    echo "$module_name normalization changed its line count" >&2
    exit 1
  fi
  rm "$roundtrip"
}

normalize_generated_import AspisCoreFieldReduceU64 no
normalize_generated_import AspisCoreFieldMulNamespaced no
normalize_generated_import AspisCoreCm31Multiplicative no
normalize_generated_import AspisCoreM31Inverse yes

# Authenticate the complete final source set immediately after normalization.
(
  cd "$staged_proof"
  shasum -a 256 -c "$staged_hashes"
)

(
  cd "$staged_proof"
  shasum -a 256 -c "$normalized_hashes"
)

for module_name in \
    M31ReduceU64Proof \
    M31MulProof \
    CM31ExactModel \
    CM31MultiplicativeProof \
    CM31SquareProof \
    CM31MulM31Proof \
    M31InverseProof; do
  cmp "$snapshot_proof/$module_name.lean" "$staged_proof/$module_name.lean"
done

# The scoped BvEnum compatibility change intentionally omits eager
# realization because this chain does not invoke Aeneas's bv_decide tactics.
if rg -n '\b(bv_tac|bv_decide)\b' "$staged_proof"; then
  echo "the scoped Lean-4.32 chain unexpectedly invokes an Aeneas BV tactic" >&2
  exit 1
fi

(
  cd "$lean_backend"
  if [[ "$(jq -r '.packages[] | select(.name == "mathlib") | .inputRev' lake-manifest.json)" != "$MATHLIB_TAG" ]] ||
      [[ "$(jq -r '.packages[] | select(.name == "mathlib") | .rev' lake-manifest.json)" != "$MATHLIB_COMMIT" ]]; then
    echo "Lake did not resolve the exact Lean-4.32 mathlib release" >&2
    exit 1
  fi

  readonly lean_version_output="$(lake env lean --version)"
  if [[ "$lean_version_output" != *"version $LEAN_VERSION"* ]] ||
      [[ "$lean_version_output" != *"commit $LEAN_COMMIT"* ]]; then
    echo "unexpected Lean compiler: $lean_version_output" >&2
    exit 1
  fi

  lake build \
    Aeneas.Std \
    Aeneas.Tactic.RustAttributes \
    Mathlib.Data.ZMod.Basic \
    Mathlib.Algebra.QuadraticAlgebra.Basic \
    Mathlib.Algebra.Field.ZMod \
    Mathlib.FieldTheory.Finite.Basic \
    Mathlib.Tactic.NormNum.Prime \
    2>&1 | tee "$build_log"
  cmp lake-manifest.json "$work_dir/lake-manifest.before.json"
)

run_lean() {
  local module_name="$1"
  (
    cd "$lean_backend"
    lake env sh -c '
      export LEAN_PATH="$1:$LEAN_PATH"
      cd "$2"
      lean "$3.lean" -o "$1/$3.olean"
    ' sh "$olean_dir" "$staged_proof" "$module_name"
  ) 2>&1 | tee -a "$axiom_log"
}

for module_name in "${modules[@]}"; do
  echo "Lean 4.32: compiling $module_name"
  run_lean "$module_name"
done

readonly hand_proofs=(
  M31ReduceU64Proof.lean
  M31MulProof.lean
  CM31ExactModel.lean
  CM31MultiplicativeProof.lean
  CM31SquareProof.lean
  CM31MulM31Proof.lean
  M31InverseProof.lean
)
if rg -n \
    '\b(sorry|admit|axiom|opaque|unsafe|extern|native_decide|sorryAx|ofReduceBool)\b|set_option[[:space:]]+maxHeartbeats|set_option[[:space:]]+maxRecDepth' \
    "${hand_proofs[@]/#/$staged_proof/}"; then
  echo "forbidden construct in a hand-written Lean-4.32 proof" >&2
  exit 1
fi

readonly generated_models=(
  AspisCoreFieldReduceU64.lean
  AspisCoreFieldMulNamespaced.lean
  AspisCoreCm31Multiplicative.lean
  AspisCoreM31Inverse.lean
)
if rg -n \
    '\b(sorry|admit|axiom|opaque|unsafe|extern|native_decide|sorryAx|ofReduceBool)\b' \
    "${generated_models[@]/#/$staged_proof/}"; then
  echo "forbidden construct in a generated Lean-4.32 model" >&2
  exit 1
fi

if rg -n '\b(sorryAx|ofReduceBool)\b' "$axiom_log"; then
  echo "forbidden axiom reached a Lean-4.32 proof report" >&2
  exit 1
fi

# Inspect every emitted report, including helper and negative-test theorems.
# Whitespace and Lean's line wrapping are ignored; no identifier outside the
# approved kernel base may occur.
perl -0777 -e '
  my $reports = 0;
  my $bad = 0;
  my %allowed = map { $_ => 1 } qw(propext Classical.choice Quot.sound);
  while (<>) {
    while (/depends on axioms:\s*\[([^\]]*)\]/g) {
      $reports += 1;
      for my $token (split /,/, $1) {
        $token =~ s/^\s+|\s+$//g;
        if (!$allowed{$token}) {
          print STDERR "unexpected axiom token: $token\n";
          $bad = 1;
        }
      }
    }
  }
  if ($reports != 30) {
    print STDERR "expected 30 #print axioms reports, got $reports\n";
    $bad = 1;
  }
  exit $bad;
' "$axiom_log"

readonly expected_axiom_reports=(
  AspisAeneasM31ReduceU64.shift31_val
  AspisAeneasM31ReduceU64.rawM31ReduceU64_canonical
  AspisAeneasM31ReduceU64.residue_rawM31ReduceU64
  AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds
  AspisAeneasM31Mul.namespaced_reduce_u64_eq
  AspisAeneasM31Mul.extracted_product_val
  AspisAeneasM31Mul.extracted_m31_mul_corresponds
  AspisAeneasCM31Multiplicative.extracted_reduce_u64_eq_existing
  AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
  AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds
  AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds
  AspisAeneasCM31Multiplicative.extracted_cm31_mul_corresponds
  AspisAeneasCM31Multiplicative.wrong_swapped_real_sub_breaks_at_i
  AspisAeneasCM31Multiplicative.wrong_cross_term_sign_breaks_at_i
  AspisAeneasCM31Square.extracted_cm31_square_corresponds
  AspisAeneasCM31Square.subtraction_order_is_load_bearing
  AspisAeneasCM31Square.imaginary_doubling_is_load_bearing
  AspisAeneasCM31MulM31.extracted_cm31_mul_m31_corresponds
  AspisAeneasCM31MulM31.scalar_limb_order_is_load_bearing
  AspisAeneasM31Inverse.extracted_reduce_u64_eq_existing
  AspisAeneasM31Inverse.extracted_m31_mul_corresponds
  AspisAeneasM31Inverse.extracted_square_n_loop_corresponds
  AspisAeneasM31Inverse.extracted_square_n_corresponds
  AspisAeneasM31Inverse.canonical_raw_ne_zero_is_residue_ne_zero
  AspisAeneasM31Inverse.pow_m31_sub_two_eq_inv
  AspisAeneasM31Inverse.extracted_m31_inv_zero_assertion_failure
  AspisAeneasM31Inverse.wrong_t28_dependency_changes_exponent
  AspisAeneasM31Inverse.wrong_t28_dependency_changes_final_exponent
  AspisAeneasM31Inverse.extracted_m31_inv_corresponds
  AspisAeneasM31Inverse.extracted_m31_inv_assertion_failure_iff_zero
)
for theorem_name in "${expected_axiom_reports[@]}"; do
  report_count="$(grep -Fc "'$theorem_name' depends on axioms:" "$axiom_log" || true)"
  if [[ "$report_count" -ne 1 ]]; then
    echo "expected exactly one axiom report for $theorem_name, got $report_count" >&2
    exit 1
  fi
done

for module_name in "${modules[@]}"; do
  if [[ ! -s "$olean_dir/$module_name.olean" ]]; then
    echo "missing Lean-4.32 object for $module_name" >&2
    exit 1
  fi
done

# Detect any mutation of the compiled source set or its authenticated inputs
# during the build.  The live Rust source is checked separately because the
# correspondence claim is deliberately about the current workspace blob.
(
  cd "$staged_proof"
  shasum -a 256 -c "$staged_hashes"
)
authenticate_snapshot
if [[ "$(git hash-object "$live_field_source")" != "$FIELD_SOURCE_BLOB" ]]; then
  echo "live field.rs changed from the source blob authenticated by this run" >&2
  exit 1
fi
require_sha256 "$FIELD_SOURCE_SHA256" "$live_field_source" "live field.rs"

echo "Lean-4.32 CM31 multiplicative + M31 inverse chain: PASS"
echo "Aeneas: $AENEAS_COMMIT"
echo "Lean: $LEAN_VERSION ($LEAN_COMMIT)"
echo "mathlib: $MATHLIB_TAG ($MATHLIB_COMMIT)"
