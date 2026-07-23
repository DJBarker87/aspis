#!/bin/sh
set -eu

readonly script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
readonly workspace=$(CDPATH= cd -- "$script_dir/../.." && pwd)
readonly mle_dir="$workspace/aeneas-verif/multilinear-eval"
readonly lean_bin="/Users/dominic/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean"
readonly base_checker="$workspace/aeneas-verif/scripts/check-cm31-inverse-lean432.sh"
readonly expected_source="4731d67935d225ede9bbc063fbfbafa198d3945f598fcf3ee8e742ca12f8e438"
readonly expected_llbc="9c96da16e56c41b2015115738a37ea1e6dc9ef5fcc0087fd36cc3b9eccf46f76"
readonly expected_raw="28ba054e2872da8fd650372cf14f1f40b488ecd01549bf16cc8cb15ba398bd6d"
readonly expected_merged="1afdb7aaecaf7688cd0b4fcbb35ff6952a90a960fff398efd6acd41ef083f3e9"
readonly expected_proof="ccab5d588ba7c1e8b21a098347cbc4885df965f4326d41396f9eaeac1b64eaf0"
readonly expected_bridge="d59d323c27264d1b66c8387f5262846940ead42d92e79190ac885c3ecd57e061"
readonly expected_aeneas="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_charon="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"

require_sha256() {
  expected=$1
  path=$2
  actual=$(shasum -a 256 "$path" | awk '{print $1}')
  test "$actual" = "$expected" || {
    echo "SHA-256 mismatch for $path: expected $expected, got $actual" >&2
    exit 1
  }
}

require_sha256 "$expected_source" \
  "$workspace/crates/aspis-prover/src/v5_split_layer_zero.rs"
require_sha256 "$expected_llbc" "$script_dir/llbc/component_b_relation_claims.llbc"
require_sha256 "$expected_raw" "$script_dir/generated/ComponentBRelationClaims.lean"
require_sha256 "$expected_merged" "$script_dir/proof/ComponentBRelationClaimsGenerated.lean"
require_sha256 "$expected_proof" "$script_dir/proof/ComponentBRelationClaimsProof.lean"
require_sha256 "$expected_bridge" "$script_dir/proof/ComponentBRelationClaimsTerminalBridge.lean"
test "$(git -C /private/tmp/aspis-aeneas-tools.aTcyie/aeneas rev-parse HEAD)" = "$expected_aeneas"
test "$(git -C /private/tmp/aspis-aeneas-tools.aTcyie/charon rev-parse HEAD)" = "$expected_charon"
test "$(jq -r '.has_errors' "$script_dir/llbc/component_b_relation_claims.llbc")" = false
test "$(jq -r '.translated.ordered_decls | length' \
  "$script_dir/llbc/component_b_relation_claims.llbc")" -eq 53

raw_fragment=$(mktemp /private/tmp/aspis-b-raw-fragment.XXXXXX)
merged_fragment=$(mktemp /private/tmp/aspis-b-merged-fragment.XXXXXX)
owned_aeneas=""
build_dir=""
cleanup() {
  rm -f -- "$raw_fragment" "$merged_fragment"
  if test -n "$build_dir" && test -d "$build_dir"; then
    case "$build_dir" in
      /private/tmp/aspis-b-relation-replay.*) rm -rf -- "$build_dir" ;;
      *) echo "refusing unexpected build path: $build_dir" >&2 ;;
    esac
  fi
  if test -n "$owned_aeneas" && test -d "$owned_aeneas"; then
    case "$owned_aeneas" in
      /private/tmp/aspis-aeneas-lean432-check.*) rm -rf -- "$owned_aeneas" ;;
      *) echo "refusing unexpected Aeneas path: $owned_aeneas" >&2 ;;
    esac
  fi
}
trap cleanup EXIT HUP INT TERM

awk '/^def v5_mask\.split_layer_zero\.V5_RELATION_POINT_CLAIMS/{copy=1}
  copy{print} copy && /^end aspis_prover$/{exit}' \
  "$script_dir/generated/ComponentBRelationClaims.lean" > "$raw_fragment"
awk '/^def v5_mask\.split_layer_zero\.V5_RELATION_POINT_CLAIMS/{copy=1}
  copy{print} copy && /^end aspis_prover$/{exit}' \
  "$script_dir/proof/ComponentBRelationClaimsGenerated.lean" > "$merged_fragment"
cmp "$raw_fragment" "$merged_fragment"

if grep -n -E \
    '(^|[^A-Za-z])(sorry|admit|native_decide|axiom|unsafe)([^A-Za-z_]|$)|set_option[[:space:]]+(maxHeartbeats|maxRecDepth)' \
    "$script_dir/proof"/*.lean; then
  exit 1
fi

if test -n "${ASPIS_AENEAS_432_WORK:-}"; then
  aeneas_work=$ASPIS_AENEAS_432_WORK
else
  path_file=$(mktemp /private/tmp/aspis-b-aeneas-path.XXXXXX)
  ASPIS_KEEP_LEAN432_WORK=1 ASPIS_LEAN432_PATH_FILE="$path_file" "$base_checker"
  aeneas_work=$(cat "$path_file")
  rm -f -- "$path_file"
  owned_aeneas=$aeneas_work
fi

aeneas_root="$aeneas_work/aeneas/backends/lean"
aeneas_path=$(cd "$aeneas_root" && lake env printenv LEAN_PATH)
aspis_path=$(cd "$workspace/AspisFormal" && lake env printenv LEAN_PATH)
build_dir=$(mktemp -d /private/tmp/aspis-b-relation-replay.XXXXXX)

cp "$mle_dir"/arithmetic/*.lean "$build_dir/"
cp "$mle_dir"/replay/*.lean "$build_dir/"
cp "$mle_dir"/proof/MultilinearEvalPortableCapstones.lean "$build_dir/"
cp "$script_dir"/proof/*.lean "$build_dir/"

lean_path="$build_dir:$aspis_path:$aeneas_path"
compile_log="$build_dir/compile.log"
: > "$compile_log"
compile() {
  module=$1
  echo "Lean 4.32: $module"
  (cd "$build_dir" && LEAN_PATH="$lean_path" "$lean_bin" \
    -o "$module.olean" "$module.lean") >> "$compile_log" 2>&1
}

for module in \
  AspisCoreFieldReduceU64 M31ReduceU64Proof \
  AspisCoreFieldMulNamespaced M31MulProof CM31ExactModel \
  AspisCoreCm31Multiplicative CM31MultiplicativeProof \
  MultilinearEvalWrappersTransparent MultilinearEvalProofs \
  MultilinearEvalFormula MultilinearEvalGeneratedFormula \
  MultilinearEvalOuterFormula MultilinearEvalEntryFormula \
  MultilinearEvalM31Formula MultilinearEvalWrapperProofs \
  MultilinearEvalAspisBridge MultilinearEvalPortableCapstones \
  ComponentBRelationClaimsGenerated ComponentBRelationClaimsProof \
  ComponentBRelationClaimsTerminalBridge
do
  compile "$module"
done

theorem_count=$(sed -n -E \
  's/^(@\[[^]]*\][[:space:]]+)?theorem[[:space:]]+([^[:space:]:({]+).*$/\2/p' \
  "$script_dir/proof/ComponentBRelationClaimsProof.lean" \
  "$script_dir/proof/ComponentBRelationClaimsTerminalBridge.lean" | wc -l | tr -d ' ')
print_count=$(sed -n -E \
  's/^#print axioms[[:space:]]+([^[:space:]]+).*$/\1/p' \
  "$script_dir/proof/ComponentBRelationClaimsProof.lean" \
  "$script_dir/proof/ComponentBRelationClaimsTerminalBridge.lean" | wc -l | tr -d ' ')
test "$theorem_count" -eq 6
test "$print_count" -eq 6
test "$(grep -c 'depends on axioms:' "$compile_log")" -ge 6
if grep -E 'sorryAx|ofReduceBool' "$compile_log"; then
  exit 1
fi
awk '
  /depends on axioms:/ { inside=1; sub(/^.*depends on axioms: \[/, "") }
  inside {
    closes=index($0, "]"); line=$0; sub(/].*$/, "", line)
    count=split(line, names, ",")
    for (ix=1; ix<=count; ix++) {
      name=names[ix]
      gsub(/^[[:space:]]+|[[:space:]]+$/, "", name)
      if (name != "") print name
    }
    if (closes != 0) inside=0
  }
' "$compile_log" | grep -v -E '^(propext|Classical\.choice|Quot\.sound)$' \
  > "$build_dir/unexpected-axioms.log" || true
test ! -s "$build_dir/unexpected-axioms.log"

echo "Component-B relation-claim consumer Lean-4.32 replay: PASS"
