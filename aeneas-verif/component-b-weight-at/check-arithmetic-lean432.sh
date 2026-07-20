#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly LEAN_VERSION="4.32.0"
readonly FIELD_SOURCE_BLOB="96e8c04efee6a8231adb2723dac9acf975993e06"
readonly FIELD_SOURCE_SHA256="b424ea2c70902e477a2580d683279645b3dd0423bfa1c9043494bc6a99dfad1e"
readonly SOURCE_MANIFEST_SHA256="ce7c974ff7b2272891a24cf294af43c84124eb483b4d2ad01159c9958431d471"
readonly PREPARED_LLBC_SHA256="ba87f9ce53ba80b42af963bd97341ff13b854d35734371d42b1d17ac9e6917f1"
readonly TOWER_LLBC_SHA256="69718455da84b9aa6481151b769f8020451ec2151fea921e9a4900a3da9de8c2"
readonly SUM_PRODUCTS_LLBC_SHA256="e0288da421919ca118dc08b2766b4664f7bb19626a1a415d8f6e762712656fcc"
readonly PREPARED_RAW_LEAN_SHA256="9e8a51d7f1069b39b39197732c690b58799fff504eddaf67cb5d48c17b98dec6"
readonly TOWER_RAW_LEAN_SHA256="a1dfb836699c12a784c2d4e328d300d1f8cc465d4815a097197b90cd24684769"
readonly SUM_PRODUCTS_RAW_LEAN_SHA256="d6d31be06350c5c87c1139b0b15568271c2d080b331ba5e62f480ddd30da341f"
readonly PREPARED_RETARGET_SHA256="27a2eaa5820a8d3f905ac1633d11b537108111ee3e10ff8011a77f05928ba61b"

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd -P)"
readonly arithmetic_dir="$script_dir/arithmetic-lean432"
readonly source_manifest="$arithmetic_dir/SOURCE_MANIFEST.sha256"
readonly base_checker="$verification_dir/scripts/check-cm31-inverse-lean432.sh"
readonly field_source="$workspace_dir/crates/aspis-core/src/field.rs"
readonly llbc_dir="$verification_dir/llbc"
readonly prepared_llbc="$llbc_dir/aspis_core_prepared_qm31.llbc"
readonly tower_llbc="$llbc_dir/aspis_core_tower_embeddings.llbc"
readonly sum_products_llbc="$llbc_dir/aspis_core_qm31_sum_products_small.llbc"

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
  AspisCoreFieldAddSubNeg
  QM31AddSubNegProof
  HalfShiftCountAdapter
  MulPow2ShiftAdapter
  ReducerShiftCountAdapter
  AspisCoreHalf
  HalfProof
  AspisCoreMulPow2
  MulPow2Proof
  AspisCorePublicReducers
  PublicU64ReducersProof
  PublicU128ReducerProof
  QM31MulProof
  AspisCoreTowerEmbeddings
  TowerEmbeddingsProof
  AspisCoreQm31SquareScalars
  QM31SquareScalarsProof
  AspisCoreQm31SumProductsSmall
  SumProductsArithmetic
  AspisCoreIsZero
  IsZeroProof
  AspisCorePow
  M31PowProof
  CM31PowProof
  QM31PowProof
  PowNonVacuity
)

for command_name in git jq lake lean perl rg shasum; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 2
  fi
done

if [[ ! -x "$base_checker" ]] || [[ ! -f "$source_manifest" ]] ||
    [[ ! -f "$field_source" ]] || [[ ! -f "$prepared_llbc" ]] ||
    [[ ! -f "$tower_llbc" ]] || [[ ! -f "$sum_products_llbc" ]]; then
  echo "incomplete durable Lean-4.32 arithmetic bundle" >&2
  exit 2
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

authenticate_sources() {
  require_sha256 "$SOURCE_MANIFEST_SHA256" "$source_manifest" \
    "arithmetic source manifest"
  (
    cd "$arithmetic_dir"
    shasum -a 256 -c "$(basename "$source_manifest")"
  )
  if [[ "$(git hash-object "$field_source")" != "$FIELD_SOURCE_BLOB" ]]; then
    echo "field.rs is not the source blob authenticated by the extraction" >&2
    exit 1
  fi
  require_sha256 "$FIELD_SOURCE_SHA256" "$field_source" "field.rs"

  require_sha256 "$PREPARED_LLBC_SHA256" "$prepared_llbc" \
    "Prepared QM31 LLBC"
  require_sha256 "$TOWER_LLBC_SHA256" "$tower_llbc" \
    "tower-embedding LLBC"
  require_sha256 "$SUM_PRODUCTS_LLBC_SHA256" "$sum_products_llbc" \
    "small-product reconstruction LLBC"

  jq -e '
    .has_errors == false and
    (.translated.type_decls | length) == 14 and
    (.translated.fun_decls | length) == 33 and
    (.translated.global_decls | length) == 2 and
    (.translated.ordered_decls | length) == 61 and
    .translated.options.preset == "Aeneas" and
    .translated.options.start_from == [
      "aspis_core::field::_::new",
      "aspis_core::field::_::mul",
      "aspis_core::field::mul_by_r"
    ]
  ' "$prepared_llbc" >/dev/null
  jq -e '
    .has_errors == false and
    (.translated.type_decls | length) == 13 and
    (.translated.fun_decls | length) == 24 and
    (.translated.global_decls | length) == 4 and
    (.translated.ordered_decls | length) == 49 and
    .translated.options.preset == "Aeneas" and
    .translated.options.start_from == [
      "aspis_core::field::_::new",
      "aspis_core::field::_::from_m31",
      "aspis_core::field::_::from_cm31"
    ]
  ' "$tower_llbc" >/dev/null
  jq -e '
    .has_errors == false and
    (.translated.type_decls | length) == 48 and
    (.translated.fun_decls | length) == 155 and
    (.translated.global_decls | length) == 6 and
    (.translated.ordered_decls | length) == 52 and
    .translated.options.preset == "Aeneas" and
    .translated.options.start_from == [
      "aspis_core::field::qm31_from_karatsuba_channel_sums",
      "aspis_core::field::qm31_sum_products_small",
      "aspis_core::field::qm31_sum_products2",
      "aspis_core::field::qm31_sum_products3",
      "aspis_core::field::qm31_sum_products4"
    ]
  ' "$sum_products_llbc" >/dev/null

  for llbc_file in "$prepared_llbc" "$tower_llbc" "$sum_products_llbc"; do
    jq -ej '
      .translated.files[]
      | select(.name.Local == "crates/aspis-core/src/field.rs")
      | .contents
    ' "$llbc_file" | cmp -s - "$field_source"
  done
}

authenticate_sources

owned_work=""
path_file=""
cleanup() {
  if [[ -n "$path_file" ]] && [[ -f "$path_file" ]]; then
    rm "$path_file"
  fi
  if [[ -n "$owned_work" ]] &&
      [[ "${ASPIS_KEEP_LEAN432_WORK:-0}" != "1" ]]; then
    case "$owned_work" in
      /private/tmp/aspis-aeneas-lean432-check.*) rm -rf "$owned_work" ;;
      *) echo "refusing to remove unexpected work path: $owned_work" >&2 ;;
    esac
  elif [[ -n "$owned_work" ]]; then
    echo "LEAN432_WORK_DIR=$owned_work"
  fi
}
trap cleanup EXIT

if [[ -n "${ASPIS_AENEAS_432_WORK:-}" ]]; then
  work_dir="$(cd "$ASPIS_AENEAS_432_WORK" && pwd -P)"
else
  path_file="$(mktemp /private/tmp/aspis-level3-path.XXXXXX)"
  ASPIS_KEEP_LEAN432_WORK=1 \
  ASPIS_LEAN432_PATH_FILE="$path_file" \
    "$base_checker"
  work_dir="$(cat "$path_file")"
  owned_work="$work_dir"
fi

readonly work_dir
readonly aeneas_checkout="$work_dir/aeneas"
readonly lean_backend="$aeneas_checkout/backends/lean"
if [[ ! -d "$lean_backend" ]] ||
    [[ "$(git -C "$aeneas_checkout" rev-parse HEAD)" != "$AENEAS_COMMIT" ]]; then
  echo "the supplied Lean-4.32 work tree is not the pinned Aeneas checkout" >&2
  exit 1
fi

readonly lean_version_output="$(cd "$lean_backend" && lake env lean --version)"
if [[ "$lean_version_output" != *"version $LEAN_VERSION"* ]]; then
  echo "unexpected Lean compiler: $lean_version_output" >&2
  exit 1
fi

readonly run_dir="$(mktemp -d "$work_dir/component-b-arithmetic.XXXXXX")"
readonly olean_dir="$run_dir/olean"
readonly prepared_olean_dir="$run_dir/prepared-olean"
readonly prepared_source_dir="$run_dir/prepared-source"
readonly axiom_log="$run_dir/axioms.log"
readonly prepared_dependency_log="$run_dir/prepared-dependencies.log"
mkdir -p "$olean_dir" "$prepared_olean_dir" "$prepared_source_dir"

verify_normalized_generated_raw() {
  local module_name="$1"
  local raw_sha256="$2"
  local restore_high_limits="$3"
  local remove_rust_attributes="$4"
  local normalized="$arithmetic_dir/$module_name.lean"
  local reconstructed="$run_dir/$module_name.raw.lean"

  cp "$normalized" "$reconstructed"
  if [[ "$(grep -c '^import Aeneas\.Std$' "$reconstructed")" -ne 1 ]]; then
    echo "$module_name has an unexpected normalized import" >&2
    exit 1
  fi
  perl -0pi -e 's/^import Aeneas\.Std\n/import Aeneas\n/m' "$reconstructed"
  if [[ "$remove_rust_attributes" == "yes" ]]; then
    if [[ "$(grep -c '^import Aeneas\.Tactic\.RustAttributes$' \
        "$reconstructed")" -ne 1 ]]; then
      echo "$module_name has an unexpected Rust-attribute import" >&2
      exit 1
    fi
    perl -0pi -e \
      's/^import Aeneas\.Tactic\.RustAttributes\n//m' "$reconstructed"
  fi
  if [[ "$restore_high_limits" == "yes" ]]; then
    if [[ "$(grep -c '^set_option maxHeartbeats 200000$' "$reconstructed")" -ne 1 ]] ||
        [[ "$(grep -c '^set_option maxRecDepth 1000$' "$reconstructed")" -ne 1 ]]; then
      echo "$module_name has unexpected normalized generated limits" >&2
      exit 1
    fi
    perl -0pi -e '
      s/^set_option maxHeartbeats 200000$/set_option maxHeartbeats 1000000/m;
      s/^set_option maxRecDepth 1000$/set_option maxRecDepth 2048/m;
    ' "$reconstructed"
  fi
  require_sha256 "$raw_sha256" "$reconstructed" \
    "$module_name reverse-normalized raw Aeneas output"
}

# These byte-for-byte reverse checks make the 4.32 normalization mechanical:
# only the broad import changes, the generated loop-attribute import where it
# is required, and the two generated resource defaults reduced from
# 1000000/2048 to the standard 200000/1000 after replay.
verify_normalized_generated_raw \
  AspisCorePreparedQM31 "$PREPARED_RAW_LEAN_SHA256" yes no
verify_normalized_generated_raw \
  AspisCoreTowerEmbeddings "$TOWER_RAW_LEAN_SHA256" yes no
verify_normalized_generated_raw \
  AspisCoreQm31SumProductsSmall "$SUM_PRODUCTS_RAW_LEAN_SHA256" no yes

run_lean() {
  local module_name="$1"
  (
    cd "$lean_backend"
    lake env sh -c '
      export LEAN_PATH="$1:$LEAN_PATH"
      cd "$2"
      lean "$3.lean" -o "$1/$3.olean"
    ' sh "$olean_dir" "$arithmetic_dir" "$module_name"
  ) 2>&1 | tee -a "$axiom_log"
}

for module_name in "${modules[@]}"; do
  echo "Lean 4.32 arithmetic: $module_name"
  run_lean "$module_name"
done

# The Prepared extraction was generated from a broader Charon closure whose
# namespace intentionally matches the earlier CM31 multiplication model.  It
# is therefore replayed in an isolated object directory.  The only dependency
# retarget is the generated-module import in the already-audited CM31 proof;
# reverse substitution must recover that source byte-for-byte, and the exact
# retargeted file hash is pinned here.
perl -pe \
  's/^import AspisCoreCm31Multiplicative$/import AspisCorePreparedQM31/' \
  "$arithmetic_dir/CM31MultiplicativeProof.lean" > \
  "$prepared_source_dir/CM31MultiplicativeProof.lean"
require_sha256 "$PREPARED_RETARGET_SHA256" \
  "$prepared_source_dir/CM31MultiplicativeProof.lean" \
  "Prepared dependency retarget"
perl -pe \
  's/^import AspisCorePreparedQM31$/import AspisCoreCm31Multiplicative/' \
  "$prepared_source_dir/CM31MultiplicativeProof.lean" | \
  cmp -s - "$arithmetic_dir/CM31MultiplicativeProof.lean"

run_prepared_lean() {
  local module_name="$1"
  local source_dir="$2"
  local log_file="$3"
  (
    cd "$lean_backend"
    lake env sh -c '
      export LEAN_PATH="$1:$2:$LEAN_PATH"
      cd "$3"
      lean "$4.lean" -o "$1/$4.olean"
    ' sh "$prepared_olean_dir" "$olean_dir" "$source_dir" "$module_name"
  ) 2>&1 | tee -a "$log_file"
}

echo "Lean 4.32 arithmetic: AspisCorePreparedQM31 (isolated generated world)"
run_prepared_lean AspisCorePreparedQM31 "$arithmetic_dir" \
  "$prepared_dependency_log"
echo "Lean 4.32 arithmetic: CM31MultiplicativeProof (exact import retarget)"
run_prepared_lean CM31MultiplicativeProof "$prepared_source_dir" \
  "$prepared_dependency_log"
echo "Lean 4.32 arithmetic: QM31MulProof (isolated dependency replay)"
run_prepared_lean QM31MulProof "$arithmetic_dir" "$prepared_dependency_log"
echo "Lean 4.32 arithmetic: PreparedQM31NewMulProof"
run_prepared_lean PreparedQM31NewMulProof "$arithmetic_dir" "$axiom_log"

readonly generated_models=(
  AspisCoreCm31Multiplicative.lean
  AspisCoreFieldAddSubNeg.lean
  AspisCoreFieldMulNamespaced.lean
  AspisCoreFieldReduceU64.lean
  AspisCoreHalf.lean
  AspisCoreIsZero.lean
  AspisCoreM31Inverse.lean
  AspisCoreMulPow2.lean
  AspisCorePow.lean
  AspisCorePublicReducers.lean
  AspisCoreQm31SquareScalars.lean
  AspisCorePreparedQM31.lean
  AspisCoreTowerEmbeddings.lean
  AspisCoreQm31SumProductsSmall.lean
)

handwritten_sources=()
for lean_source in "$arithmetic_dir"/*.lean; do
  generated="no"
  for generated_name in "${generated_models[@]}"; do
    if [[ "$(basename "$lean_source")" == "$generated_name" ]]; then
      generated="yes"
      break
    fi
  done
  if [[ "$generated" == "no" ]]; then
    handwritten_sources+=("$lean_source")
  fi
done

if rg -n \
    '\b(sorry|admit|axiom|unsafe|native_decide|sorryAx|ofReduceBool)\b|set_option[[:space:]]+maxHeartbeats|set_option[[:space:]]+maxRecDepth' \
    "${handwritten_sources[@]}"; then
  echo "raised limit in a handwritten Lean-4.32 arithmetic proof" >&2
  exit 1
fi
generated_sources=("${generated_models[@]/#/$arithmetic_dir/}")
if rg -n '\b(sorry|admit|unsafe|native_decide|sorryAx|ofReduceBool)\b' \
    "${generated_sources[@]}"; then
  echo "forbidden construct in a generated Lean-4.32 arithmetic model" >&2
  exit 1
fi

# The broad Prepared and tower LLBCs each contain exactly one Aeneas
# environment declaration for core::array::from_fn.  It is retained rather
# than silently deleted.  The theorem-closure audit below rejects it (or any
# other non-approved axiom) if it becomes reachable from a capstone.
if [[ "$(rg -N '^axiom core\.array\.from_fn$' \
      "$arithmetic_dir/AspisCorePreparedQM31.lean" | wc -l | tr -d ' ')" -ne 1 ]] ||
    [[ "$(rg -N '^axiom core\.array\.from_fn$' \
      "$arithmetic_dir/AspisCoreTowerEmbeddings.lean" | wc -l | tr -d ' ')" -ne 1 ]]; then
  echo "unexpected generated core.array.from_fn classification" >&2
  exit 1
fi
if rg -n '^axiom ' \
    "$arithmetic_dir/AspisCoreQm31SumProductsSmall.lean" \
    "${generated_sources[@]:0:11}"; then
  echo "unexpected axiom declaration in a generated arithmetic model" >&2
  exit 1
fi
if rg -n '\b(sorryAx|ofReduceBool)\b' "$axiom_log"; then
  echo "forbidden axiom reached an arithmetic theorem closure" >&2
  exit 1
fi

readonly expected_reports="$(
  rg -N '^#print axioms ' "$arithmetic_dir"/*.lean | wc -l | tr -d ' '
)"
perl -0777 -e '
  my $expected = shift @ARGV;
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
    while (/does not depend on any axioms/g) {
      $reports += 1;
    }
  }
  if ($reports != $expected) {
    print STDERR "expected $expected axiom reports, got $reports\n";
    $bad = 1;
  }
  exit $bad;
' "$expected_reports" "$axiom_log"

for proof_file in \
    PreparedQM31NewMulProof.lean \
    TowerEmbeddingsProof.lean \
    SumProductsArithmetic.lean; do
  declared_theorems="$(
    sed -n 's/^theorem \([^ :(]*\).*/\1/p' "$arithmetic_dir/$proof_file" |
      LC_ALL=C sort
  )"
  printed_theorems="$(
    sed -n 's/^#print axioms \([^ ]*\).*/\1/p' "$arithmetic_dir/$proof_file" |
      LC_ALL=C sort
  )"
  if [[ "$declared_theorems" != "$printed_theorems" ]]; then
    echo "$proof_file does not audit every exported theorem" >&2
    exit 1
  fi
done

readonly new_level3_reports=(
  AspisAeneasPreparedQM31.extracted_prepared_new_establishes
  AspisAeneasPreparedQM31.extracted_prepared_mul_corresponds
  AspisAeneasPreparedQM31.extracted_new_then_prepared_mul_corresponds
  AspisAeneasTowerEmbeddings.extracted_cm31_new_corresponds
  AspisAeneasTowerEmbeddings.extracted_cm31_from_m31_corresponds
  AspisAeneasTowerEmbeddings.extracted_qm31_from_cm31_corresponds
  AspisLane5QM31SumProductsProof.extracted_qm31_from_karatsuba_channel_sums_corresponds
)
readonly new_negative_and_domain_reports=(
  AspisAeneasPreparedQM31.corrupted_cache_tooth
  AspisAeneasPreparedQM31.swapped_rows_tooth
  AspisAeneasPreparedQM31.prepared_qm31_domain_nonempty
  AspisAeneasTowerEmbeddings.swapped_cm31_new_coordinates_tooth
  AspisAeneasTowerEmbeddings.nonzero_imaginary_from_m31_tooth
  AspisAeneasTowerEmbeddings.nonzero_u_coordinate_from_cm31_tooth
  AspisAeneasTowerEmbeddings.canonical_embedding_domains_nonempty
  AspisLane5QM31SumProductsProof.reconstruct_with_two_minus_i_is_wrong
)
for theorem_name in \
    "${new_level3_reports[@]}" "${new_negative_and_domain_reports[@]}"; do
  if ! rg -q "^'$theorem_name' (depends on axioms:|does not depend on any axioms)" \
      "$axiom_log"; then
    echo "missing exact Lean-4.32 axiom report for $theorem_name" >&2
    exit 1
  fi
done

for module_name in "${modules[@]}"; do
  if [[ ! -s "$olean_dir/$module_name.olean" ]]; then
    echo "missing Lean-4.32 object for $module_name" >&2
    exit 1
  fi
done
for module_name in \
    AspisCorePreparedQM31 \
    CM31MultiplicativeProof \
    QM31MulProof \
    PreparedQM31NewMulProof; do
  if [[ ! -s "$prepared_olean_dir/$module_name.olean" ]]; then
    echo "missing isolated Lean-4.32 object for $module_name" >&2
    exit 1
  fi
done

authenticate_sources
echo "Lean-4.32 shared M31/CM31/QM31 arithmetic chain: PASS"
echo "AXIOM_REPORTS=$expected_reports"
echo "ARITHMETIC_OLEAN_DIR=$olean_dir"
