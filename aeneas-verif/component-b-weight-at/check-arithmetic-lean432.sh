#!/usr/bin/env bash
set -euo pipefail

readonly AENEAS_COMMIT="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly LEAN_VERSION="4.32.0"
readonly FIELD_SOURCE_BLOB="96e8c04efee6a8231adb2723dac9acf975993e06"
readonly FIELD_SOURCE_SHA256="b424ea2c70902e477a2580d683279645b3dd0423bfa1c9043494bc6a99dfad1e"
readonly SOURCE_MANIFEST_SHA256="8ed6cdb1479c4a3df680e615350af310baf3397e15030ab4d4ef35630b828e36"

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd -P)"
readonly arithmetic_dir="$script_dir/arithmetic-lean432"
readonly source_manifest="$arithmetic_dir/SOURCE_MANIFEST.sha256"
readonly base_checker="$verification_dir/scripts/check-cm31-inverse-lean432.sh"
readonly field_source="$workspace_dir/crates/aspis-core/src/field.rs"

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
  AspisCoreQm31SquareScalars
  QM31SquareScalarsProof
  AspisCoreIsZero
  IsZeroProof
  AspisCorePow
  M31PowProof
  CM31PowProof
  QM31PowProof
  PowNonVacuity
)

for command_name in git lake lean perl rg shasum; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 2
  fi
done

if [[ ! -x "$base_checker" ]] || [[ ! -f "$source_manifest" ]] ||
    [[ ! -f "$field_source" ]]; then
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
readonly axiom_log="$run_dir/axioms.log"
mkdir -p "$olean_dir"

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

if rg -n '\b(sorry|admit|axiom|unsafe|native_decide|sorryAx|ofReduceBool)\b' \
    "$arithmetic_dir"/*.lean; then
  echo "forbidden construct in the Lean-4.32 arithmetic bundle" >&2
  exit 1
fi
if rg -n \
    'set_option[[:space:]]+maxHeartbeats|set_option[[:space:]]+maxRecDepth' \
    "${handwritten_sources[@]}"; then
  echo "raised limit in a handwritten Lean-4.32 arithmetic proof" >&2
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

for module_name in "${modules[@]}"; do
  if [[ ! -s "$olean_dir/$module_name.olean" ]]; then
    echo "missing Lean-4.32 object for $module_name" >&2
    exit 1
  fi
done

authenticate_sources
echo "Lean-4.32 shared M31/CM31/QM31 arithmetic chain: PASS"
echo "AXIOM_REPORTS=$expected_reports"
echo "ARITHMETIC_OLEAN_DIR=$olean_dir"
