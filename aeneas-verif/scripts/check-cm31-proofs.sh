#!/usr/bin/env bash
set -euo pipefail

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly proof_dir="$verification_dir/proof"
readonly olean_dir="$proof_dir/.lake/build/lib/lean"

mkdir -p "$olean_dir"
cd "$proof_dir"

# The operation-specific Aeneas outputs intentionally reuse the `aspis_core`
# namespace.  Compile them in separate Lean processes, then compile each CM31
# composition proof against the matching generated module.
lake env lean AspisCoreFieldAdd.lean -o "$olean_dir/AspisCoreFieldAdd.olean"
lake env lean M31AddProof.lean -o "$olean_dir/M31AddProof.olean"
lake env lean CM31ExactModel.lean -o "$olean_dir/CM31ExactModel.olean"
lake env lean CM31AddProof.lean

lake env lean AspisCoreFieldSub.lean -o "$olean_dir/AspisCoreFieldSub.olean"
lake env lean M31SubProof.lean -o "$olean_dir/M31SubProof.olean"
lake env lean CM31SubProof.lean

lake env lean AspisCoreFieldNeg.lean -o "$olean_dir/AspisCoreFieldNeg.olean"
lake env lean M31NegProof.lean -o "$olean_dir/M31NegProof.olean"
lake env lean CM31NegProof.lean

lake env lean AspisCoreCm31Helpers.lean \
  -o "$olean_dir/AspisCoreCm31Helpers.olean"
lake env lean CM31DoubleProof.lean
lake env lean CM31ConjugateMulIProof.lean

if rg -n \
    '\b(sorry|admit|axiom|unsafe|native_decide)\b|set_option[[:space:]]+maxHeartbeats|set_option[[:space:]]+maxRecDepth' \
    CM31ExactModel.lean \
    CM31AddProof.lean \
    CM31SubProof.lean \
    CM31NegProof.lean \
    CM31DoubleProof.lean \
    CM31ConjugateMulIProof.lean; then
  echo "forbidden construct in a hand-written CM31 proof" >&2
  exit 1
fi
