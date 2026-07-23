#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly workspace="$(cd "$script_dir/../.." && pwd -P)"
readonly lean_bin=/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
readonly base_checker="$workspace/aeneas-verif/scripts/check-cm31-inverse-lean432.sh"
readonly arithmetic_checker="$workspace/aeneas-verif/component-b-weight-at/check-arithmetic-lean432.sh"
readonly wire_llbc="$script_dir/llbc/runtime_component_c_wire.llbc"
readonly evaluator_llbc="$script_dir/llbc/runtime_evaluator_full_v28.llbc"
readonly schedule_llbc="$script_dir/llbc/runtime_schedule.llbc"
readonly rust_source="$workspace/crates/aspis-prover/src/v5_component_c_runtime.rs"
readonly schedule_source="$workspace/crates/aspis-core/src/circle_line_merkle.rs"
readonly expected_aeneas=b59d5188c082f704a418c7cb4e52ad69328002d1
readonly expected_charon=cb50ff16b9f1066b8a97dc06da704de2da2fa41c
readonly expected_prints=55

sha256_of() { shasum -a 256 "$1" | awk '{print $1}'; }
require_sha256() {
  local expected=$1 file=$2
  test "$(sha256_of "$file")" = "$expected" || {
    echo "SHA-256 mismatch: $file" >&2
    exit 1
  }
}

for command_name in git jq lake lean perl rg shasum; do
  command -v "$command_name" >/dev/null
done
test -x "$lean_bin"
test -x "$base_checker"
test -x "$arithmetic_checker"
test "$(git -C /private/tmp/aspis-aeneas-tools.aTcyie/aeneas rev-parse HEAD)" = "$expected_aeneas"
test "$(git -C /private/tmp/aspis-aeneas-tools.aTcyie/charon rev-parse HEAD)" = "$expected_charon"

require_sha256 327be85bea18701dcb5eb9ab7d6303f3453b2e6fbc6a1de9a67b414ae87f9d76 "$rust_source"
require_sha256 25972bda8bf819ba833cba44959aed66da7e8647329e32d758b1d25add4999b3 "$wire_llbc"
require_sha256 39c71967074f797f482316317a542f5bfc3acae4a80b9909c7513acc3ac0b24c "$evaluator_llbc"
require_sha256 f14cab955f3d701f1ed85cada76db1d7b31582f71833895e63c4bde8edc93b25 \
  "$script_dir/generated/runtime_component_c_wire/RuntimeComponentCWire.lean"
require_sha256 34e41c8153010cf029c1fafb2c3411f4e7ed9daa6ff72cdd8cb7afa8093cb6f5 \
  "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/Types.lean"
require_sha256 0fb293344b82f0efb4aa424dfdd73c70b32ad18cc45c80f636c3a70ebb4ca8e2 \
  "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/FunsExternal.lean"
require_sha256 b8ff93734425e396472b58fca6b1391ff92f0f2629d47349a82c8a930aaa0399 \
  "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/Funs.lean"

jq -e '.has_errors == false and (.translated.ordered_decls | length) == 45' "$wire_llbc" >/dev/null
jq -e '.has_errors == false and (.translated.ordered_decls | length) == 339' "$evaluator_llbc" >/dev/null
jq -e '.has_errors == false and (.translated.ordered_decls | length) > 0' "$schedule_llbc" >/dev/null
jq -ej '.translated.files[] | select(.name.Local == "crates/aspis-prover/src/v5_component_c_runtime.rs") | .contents' \
  "$wire_llbc" | cmp -s - "$rust_source"
jq -ej '.translated.files[] | select(.name.Local == "crates/aspis-prover/src/v5_component_c_runtime.rs") | .contents' \
  "$evaluator_llbc" | cmp -s - "$rust_source"
jq -ej '.translated.files[] | select(.name.Local == "crates/aspis-core/src/circle_line_merkle.rs") | .contents' \
  "$schedule_llbc" | cmp -s - "$schedule_source"

build_dir=$(mktemp -d /private/tmp/aspis-c-runtime432-current.XXXXXX)
owned_work=""
cleanup() {
  find "$build_dir" -depth -delete 2>/dev/null || true
  if [[ -n "$owned_work" ]]; then
    case "$owned_work" in
      /private/tmp/aspis-aeneas-lean432-check.*) find "$owned_work" -depth -delete 2>/dev/null || true ;;
      *) echo "refusing unexpected cleanup path: $owned_work" >&2 ;;
    esac
  fi
}
trap cleanup EXIT HUP INT TERM

if [[ -n "${ASPIS_AENEAS_432_WORK:-}" ]]; then
  aeneas_work=$(cd "$ASPIS_AENEAS_432_WORK" && pwd -P)
else
  path_file=$(mktemp /private/tmp/aspis-c-runtime432-base-path.XXXXXX)
  ASPIS_KEEP_LEAN432_WORK=1 ASPIS_LEAN432_PATH_FILE="$path_file" "$base_checker"
  aeneas_work=$(cat "$path_file")
  rm -f -- "$path_file"
  owned_work=$aeneas_work
fi
readonly aeneas_root="$aeneas_work/aeneas/backends/lean"
test -d "$aeneas_root/.lake/build/lib/lean/Aeneas"

if [[ -n "${ASPIS_ARITHMETIC_OLEAN_DIR:-}" ]]; then
  arithmetic_olean=$(cd "$ASPIS_ARITHMETIC_OLEAN_DIR" && pwd -P)
else
  arithmetic_log="$build_dir/arithmetic.log"
  ASPIS_AENEAS_432_WORK="$aeneas_work" "$arithmetic_checker" | tee "$arithmetic_log"
  arithmetic_olean=$(sed -n 's/^ARITHMETIC_OLEAN_DIR=//p' "$arithmetic_log" | tail -1)
fi
test -f "$arithmetic_olean/HalfProof.olean"
test -f "$arithmetic_olean/QM31MulProof.olean"

mkdir -p "$build_dir/ComponentCRuntimeGenerated"
cp "$script_dir/generated/runtime_component_c_wire/RuntimeComponentCWire.lean" "$build_dir/"
cp "$script_dir/replay/runtime_schedule/RuntimeSchedule.lean" "$build_dir/"
cp "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated.lean" "$build_dir/"
cp "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/Types.lean" \
  "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/FunsExternal.lean" \
  "$script_dir/generated/runtime_evaluator_full_v28/ComponentCRuntimeGenerated/Funs.lean" \
  "$build_dir/ComponentCRuntimeGenerated/"
cp "$script_dir"/proof/*.lean "$build_dir/"

if rg -n '(^|[^A-Za-z_])(sorry|admit|native_decide|axiom|unsafe)([^A-Za-z_]|$)|set_option[[:space:]]+(maxHeartbeats|maxRecDepth)' \
    "$build_dir" --glob '*.lean' > "$build_dir/forbidden.log"; then
  cat "$build_dir/forbidden.log" >&2
  exit 1
fi

aeneas_path=$(cd "$aeneas_root" && lake env printenv LEAN_PATH)
aspis_path=$(cd "$workspace/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)
export LEAN_PATH="$build_dir:$arithmetic_olean:$aspis_path:$aeneas_path"
: > "$build_dir/compile.log"
modules=(
  RuntimeComponentCWire RuntimeSchedule
  ComponentCRuntimeGenerated.Types ComponentCRuntimeGenerated.FunsExternal
  ComponentCRuntimeGenerated.Funs ComponentCRuntimeGenerated
  RuntimePackerCorrespondence RuntimeScheduleCorrespondence
  RuntimeScheduleValidatorCorrespondence RuntimeValidatedScheduleBridge
  RuntimeEvaluatorSourceAuthentic RuntimeFoldPrimitiveReduction
  RuntimeFoldPrimitiveInstantiation RuntimeFoldPrimitiveInstantiationAudit
  RuntimeLaterFibreCorrespondence RuntimeDownstreamMaintainedBridge
)
for module in "${modules[@]}"; do
  module_path=${module//./\/}
  source_file="$build_dir/$module_path.lean"
  output_file="$build_dir/$module_path.olean"
  if ! (cd "$build_dir" && "$lean_bin" -j 1 -o "$output_file" "$source_file") \
      >> "$build_dir/compile.log" 2>&1; then
    tail -200 "$build_dir/compile.log" >&2
    exit 1
  fi
done

print_count=$(rg -c '^#print axioms ' "$script_dir"/proof/*.lean | awk -F: '{n += $2} END {print n+0}')
test "$print_count" -eq "$expected_prints"
test "$(grep -E -c 'depends on axioms:|does not depend on any axioms' "$build_dir/compile.log")" \
  -eq "$expected_prints"
if rg 'sorryAx|ofReduceBool' "$build_dir/compile.log"; then exit 1; fi
awk '
  /depends on axioms:/ { inside=1; sub(/^.*depends on axioms: \[/, "") }
  inside {
    closes=index($0, "]"); line=$0; sub(/].*$/, "", line)
    count=split(line, names, ",")
    for (i=1; i<=count; i++) {
      name=names[i]; gsub(/^[[:space:]]+|[[:space:]]+$/, "", name)
      if (name != "") print name
    }
    if (closes != 0) inside=0
  }
' "$build_dir/compile.log" | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' \
  > "$build_dir/unexpected-axioms.log" || true
test ! -s "$build_dir/unexpected-axioms.log"

echo "Component-C source-authentic runtime correspondence Lean-4.32 replay: PASS ($expected_prints axiom audits)"
