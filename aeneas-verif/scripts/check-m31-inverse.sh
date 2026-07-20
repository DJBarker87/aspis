#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly proof_dir="$verification_dir/proof"
readonly olean_dir="$proof_dir/.lake/build/lib/lean"
readonly llbc_file="$verification_dir/llbc/aspis_core_m31_inverse.llbc"
readonly generated_lean="$proof_dir/AspisCoreM31Inverse.lean"
readonly work_dir="$(mktemp -d /private/tmp/aspis-m31-inverse-check.XXXXXX)"
readonly axiom_log="$work_dir/axioms.log"
trap 'rm -rf "$work_dir"' EXIT

run_lean() {
  lake env lean "$@" 2>&1 | tee -a "$axiom_log"
}

mkdir -p "$olean_dir"
cd "$proof_dir"

run_lean AspisCoreFieldReduceU64.lean \
  -o "$olean_dir/AspisCoreFieldReduceU64.olean"
run_lean M31ReduceU64Proof.lean \
  -o "$olean_dir/M31ReduceU64Proof.olean"
run_lean AspisCoreFieldMulNamespaced.lean \
  -o "$olean_dir/AspisCoreFieldMulNamespaced.olean"
run_lean M31MulProof.lean \
  -o "$olean_dir/M31MulProof.olean"
run_lean AspisCoreM31Inverse.lean \
  -o "$olean_dir/AspisCoreM31Inverse.olean"
run_lean M31InverseProof.lean

readonly inv_id="$(jq -er '
  [.translated.fun_decls[]
    | select(.item_meta.span.data.file_id == 0)
    | select(.item_meta.span.data.beg.line == 154)
    | select(.item_meta.span.data.end.line == 170)
    | select(.item_meta.source_text
        | startswith("pub fn inv(self) -> M31 {"))
    | .def_id]
  | if length == 1 then .[0]
    else error("expected exactly one production M31::inv declaration")
    end
' "$llbc_file")"

jq -e --argjson inv_id "$inv_id" '
  (.translated.type_decls | length) == 47 and
  (.translated.fun_decls | length) == 160 and
  (.translated.global_decls | length) == 6 and
  (.translated.ordered_decls | length) == 35 and
  (.translated.ordered_decls[-1] == {"Fun": {"NonRec": $inv_id}})
' "$llbc_file" >/dev/null

grep -Fq "Source: 'crates/aspis-core/src/field.rs', lines 154:4-170:5" \
  "$generated_lean"
grep -Fq "def field.square_n_loop" "$generated_lean"
grep -Fq "partial_fixpoint" "$generated_lean"
grep -Fq "def field.M31.inv (self : field.M31)" "$generated_lean"
grep -Fq "massert (self != 0#u32)" "$generated_lean"
if grep -Fq "def field.CM31.inv" "$generated_lean" ||
    grep -Fq "def field.QM31.inv" "$generated_lean" ||
    grep -Fq "inv_with" "$generated_lean"; then
  echo "unrelated extension-field inverse entered the checked model" >&2
  exit 1
fi

if rg -n \
    '\b(sorry|admit|axiom|opaque|unsafe|extern|native_decide|sorryAx|ofReduceBool)\b|set_option[[:space:]]+maxHeartbeats|set_option[[:space:]]+maxRecDepth' \
    M31InverseProof.lean \
    M31ReduceU64Proof.lean \
    M31MulProof.lean; then
  echo "forbidden construct in a hand-written M31 inverse dependency" >&2
  exit 1
fi

if rg -n '\b(sorry|admit|axiom|opaque|unsafe|extern|native_decide|sorryAx|ofReduceBool)\b' \
    AspisCoreM31Inverse.lean \
    AspisCoreFieldReduceU64.lean \
    AspisCoreFieldMulNamespaced.lean; then
  echo "forbidden construct in the generated inverse chain" >&2
  exit 1
fi

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
  "AspisAeneasM31Inverse.extracted_square_n_loop_corresponds"
  "AspisAeneasM31Inverse.extracted_square_n_corresponds"
  "AspisAeneasM31Inverse.extracted_m31_inv_zero_assertion_failure"
  "AspisAeneasM31Inverse.wrong_t28_dependency_changes_exponent"
  "AspisAeneasM31Inverse.wrong_t28_dependency_changes_final_exponent"
  "AspisAeneasM31Inverse.extracted_m31_inv_corresponds"
  "AspisAeneasM31Inverse.extracted_m31_inv_assertion_failure_iff_zero"
)
for theorem_name in "${expected_axiom_reports[@]}"; do
  if ! grep -Fq "'$theorem_name' depends on axioms:" "$axiom_log"; then
    echo "missing axiom report for $theorem_name" >&2
    exit 1
  fi
done
