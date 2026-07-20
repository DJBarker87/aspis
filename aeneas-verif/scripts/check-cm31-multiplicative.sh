#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly proof_dir="$verification_dir/proof"
readonly olean_dir="$proof_dir/.lake/build/lib/lean"
readonly llbc_file="$verification_dir/llbc/aspis_core_cm31_multiplicative.llbc"
readonly work_dir="$(mktemp -d /private/tmp/aspis-cm31-mult-check.XXXXXX)"
readonly axiom_log="$work_dir/axioms.log"
trap 'rm -rf "$work_dir"' EXIT

run_lean() {
  lake env lean "$@" 2>&1 | tee -a "$axiom_log"
}

mkdir -p "$olean_dir"
cd "$proof_dir"

# Rebuild every generated/proved dependency needed by the unified CM31
# multiplicative proof without changing the shared Lake root list.
run_lean AspisCoreFieldReduceU64.lean \
  -o "$olean_dir/AspisCoreFieldReduceU64.olean"
run_lean M31ReduceU64Proof.lean \
  -o "$olean_dir/M31ReduceU64Proof.olean"
run_lean AspisCoreFieldMulNamespaced.lean \
  -o "$olean_dir/AspisCoreFieldMulNamespaced.olean"
run_lean M31MulProof.lean \
  -o "$olean_dir/M31MulProof.olean"
run_lean CM31ExactModel.lean \
  -o "$olean_dir/CM31ExactModel.olean"
run_lean AspisCoreCm31Multiplicative.lean \
  -o "$olean_dir/AspisCoreCm31Multiplicative.olean"
run_lean CM31MultiplicativeProof.lean \
  -o "$olean_dir/CM31MultiplicativeProof.olean"
run_lean CM31SquareProof.lean
run_lean CM31MulM31Proof.lean

jq -e '
    (.translated.type_decls | length) == 8 and
    (.translated.fun_decls | length) == 21 and
    (.translated.global_decls | length) == 1 and
    (.translated.ordered_decls | length) == 35
  ' "$llbc_file" >/dev/null

if rg -n \
    '\b(sorry|admit|axiom|opaque|unsafe|extern|native_decide|sorryAx|ofReduceBool)\b|set_option[[:space:]]+maxHeartbeats|set_option[[:space:]]+maxRecDepth' \
    CM31MultiplicativeProof.lean \
    CM31SquareProof.lean \
    CM31MulM31Proof.lean \
    CM31ExactModel.lean \
    M31ReduceU64Proof.lean \
    M31MulProof.lean; then
  echo "forbidden construct in a hand-written CM31 multiplicative proof" >&2
  exit 1
fi

if rg -n '\b(sorry|admit|axiom|opaque|unsafe|extern|native_decide|sorryAx|ofReduceBool)\b' \
    AspisCoreCm31Multiplicative.lean \
    AspisCoreFieldReduceU64.lean \
    AspisCoreFieldMulNamespaced.lean; then
  echo "forbidden construct in the generated/base multiplication chain" >&2
  exit 1
fi

# Every `#print axioms` report emitted by the checked proof files must contain
# only the project-approved kernel base.  Whitespace and line wrapping are
# deliberately ignored; any other identifier makes the gate fail.
perl -0777 -e '
  my $bad = 0;
  while (<>) {
    while (/depends on axioms:\s*\[([^\]]*)\]/g) {
      my $rest = $1;
      $rest =~ s/(?:propext|Classical\.choice|Quot\.sound)//g;
      $rest =~ s/[\s,]//g;
      if (length $rest) {
        print STDERR "unexpected axiom token(s): $rest\n";
        $bad = 1;
      }
    }
  }
  exit $bad;
' "$axiom_log"

readonly expected_axiom_reports=(
  "AspisAeneasM31ReduceU64.extracted_reduce_u64_corresponds"
  "AspisAeneasM31Mul.extracted_m31_mul_corresponds"
  "AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds"
  "AspisAeneasCM31Multiplicative.extracted_m31_sub_corresponds"
  "AspisAeneasCM31Multiplicative.extracted_m31_mul_corresponds"
  "AspisAeneasCM31Multiplicative.extracted_cm31_mul_corresponds"
  "AspisAeneasCM31Square.extracted_cm31_square_corresponds"
  "AspisAeneasCM31MulM31.extracted_cm31_mul_m31_corresponds"
)
for theorem_name in "${expected_axiom_reports[@]}"; do
  if ! grep -Fq "'$theorem_name' depends on axioms:" "$axiom_log"; then
    echo "missing axiom report for $theorem_name" >&2
    exit 1
  fi
done
