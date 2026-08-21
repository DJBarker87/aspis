#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated/V5TranscriptRelationHelper"
readonly transcript_proof="$bundle/proof/V5TranscriptRelationSourceProof.lean"
readonly final_join_proof="$bundle/proof/V5TranscriptRelationFinalJoin.lean"
readonly normalization_patch="$bundle/import-normalization/V5RelationCallerGenerated-for-join.patch"
readonly acceptance_bundle="$root/aeneas-verif/v5-relation-acceptance-20260815"
readonly acceptance_caller="$acceptance_bundle/generated/V5RelationCallerGenerated.lean"
readonly acceptance_proof="$acceptance_bundle/proof/V5RelationAcceptanceSourceProof.lean"

readonly lean_bin="${LEAN432_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}"
readonly lake_bin="${LAKE432_BIN:-$(dirname "$lean_bin")/lake}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Aeneas Lean 4.32 library}"
readonly aeneas_path="${AENEAS_LEAN_PATH:-$aeneas_lib}"
readonly formal_build_root="${ASPIS_FORMAL_BUILD_ROOT:-$root}"

check_blob() {
  local expected=$1
  local path=$2
  local actual
  actual=$(git -C / hash-object --no-filters "$root/$path")
  if [[ "$actual" != "$expected" ]]; then
    echo "source identity mismatch: $path" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 1
  fi
}

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Data/Discriminant.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/RustAttributes.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/Simp/SimpScalar.olean" ]]

# Bind this focused replay to both raw Aeneas snapshots, the maintained model
# sources, the explicit import-only normalization, and the joined theorem.
check_blob ff2c2318274298244b47e01e2ca1690a7435ff3c \
  aeneas-verif/v5-relation-acceptance-20260815/generated/V5RelationCallerGenerated.lean
check_blob 61044bf7ada9152f33aa1e228761c159d7fcca46 \
  aeneas-verif/v5-relation-acceptance-20260815/proof/V5RelationAcceptanceSourceProof.lean
check_blob a1d3b661d4cae680027fd2236422042774c66d94 \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/TypesExternal.lean
check_blob 9dff5ad45b5c7f506d55b0dc3971134039fba8e6 \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/Types.lean
check_blob e8e80f86c38a2a5562330b34fd53f2defc840ebe \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/FunsExternal.lean
check_blob cb672ec424bfbff342ef4ef2d5203ee87d145185 \
  aeneas-verif/v5-transcript-relation-source-20260820/generated/V5TranscriptRelationHelper/Funs.lean
check_blob 938009384a7ad09a13d57541b8d327ada67bbdd1 \
  aeneas-verif/v5-transcript-relation-source-20260820/proof/V5TranscriptRelationSourceProof.lean
check_blob bd965e686efa6c2b4bd29c16efc173a3dc7ab688 \
  aeneas-verif/v5-transcript-relation-source-20260820/import-normalization/V5RelationCallerGenerated-for-join.patch
check_blob cf809590ce8f89ac83b1e72f4e7ec0a80081d72b \
  aeneas-verif/v5-transcript-relation-source-20260820/proof/V5TranscriptRelationFinalJoin.lean
check_blob 8ca023e0a55d300c3ff22690c162b2dc4f1502cc \
  AspisFormal/AspisFormal/V5TranscriptConnection.lean
check_blob 92d4a73b86b80cad89365610172e1687fecb2c05 \
  AspisFormal/AspisFormal/V5TranscriptSourceAdapter.lean

if [[ -n "${V5_TRANSCRIPT_FINAL_JOIN_OUT:-}" ]]; then
  out=$V5_TRANSCRIPT_FINAL_JOIN_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/v5-transcript-final-join.XXXXXX")
fi
readonly out
readonly olean="$out/olean"
readonly formal_overlay="$out/formal-overlay"
readonly join_source="$out/join-source"
readonly log="$out/replay.log"
mkdir -p "$olean/V5TranscriptRelationHelper" "$formal_overlay/AspisFormal" \
  "$join_source"
: > "$log"

formal_path=$(cd "$formal_build_root/AspisFormal" && \
  NO_DNA=1 "$lake_bin" env printenv LEAN_PATH)
readonly formal_path

formal_package_dir=
old_ifs=$IFS
IFS=:
for candidate in $formal_path; do
  if [[ -f "$candidate/AspisFormal/V5NonceWorkAuthentication.olean" ]]; then
    formal_package_dir="$candidate/AspisFormal"
    break
  fi
done
IFS=$old_ifs
readonly formal_package_dir
[[ -n "$formal_package_dir" ]]

# A sparse namespace directory masks later LEAN_PATH entries. Populate this
# overlay with symlinks to the selected build, then replace only the two exact
# modules rebuilt below.
for existing in "$formal_package_dir"/*; do
  ln -s "$existing" "$formal_overlay/AspisFormal/"
done
rm -f "$formal_overlay/AspisFormal/V5TranscriptConnection.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptConnection.ilean" \
  "$formal_overlay/AspisFormal/V5TranscriptConnection.c" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.ilean" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.c"

compile() {
  local target=$1
  local source=$2
  echo "COMPILE $target" | tee -a "$log"
  LEAN_PATH="$olean:$bundle/generated:$formal_overlay:$formal_path:$aeneas_path" \
    "$lean_bin" -j 1 -o "$olean/$target.olean" "$source" >> "$log" 2>&1
}

compile V5TranscriptRelationHelper/TypesExternal "$generated/TypesExternal.lean"
compile V5TranscriptRelationHelper/Types "$generated/Types.lean"
compile V5TranscriptRelationHelper/FunsExternal "$generated/FunsExternal.lean"
compile V5TranscriptRelationHelper/Funs "$generated/Funs.lean"
compile V5TranscriptRelationSourceProof "$transcript_proof"

# Rebuild these exact maintained sources in the isolated output. Compile the
# first module outside the overlay namespace, then install its object there.
echo "COMPILE AspisFormal/V5TranscriptConnection" | tee -a "$log"
LEAN_PATH="$formal_overlay:$formal_path:$aeneas_path" \
  "$lean_bin" -j 1 -o "$out/V5TranscriptConnection.olean" \
  "$root/AspisFormal/AspisFormal/V5TranscriptConnection.lean" >> "$log" 2>&1
mv "$out/V5TranscriptConnection.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptConnection.olean"

echo "COMPILE AspisFormal/V5TranscriptSourceAdapter" | tee -a "$log"
LEAN_PATH="$formal_overlay:$formal_path:$aeneas_path" \
  "$lean_bin" -j 1 -o "$out/V5TranscriptSourceAdapter.olean" \
  "$root/AspisFormal/AspisFormal/V5TranscriptSourceAdapter.lean" >> "$log" 2>&1
mv "$out/V5TranscriptSourceAdapter.olean" \
  "$formal_overlay/AspisFormal/V5TranscriptSourceAdapter.olean"

# The independent generated modules both declare ProgramError with Aeneas's
# discriminant macro. That macro chooses the same process-global instance name.
# Neither joined proof computes this discriminant, so remove only that attribute
# from a temporary copy and verify that no other byte changed.
cp "$acceptance_caller" "$join_source/V5RelationCallerGenerated.lean"
git -C "$join_source" init -q
git -C "$join_source" apply --check "$normalization_patch"
git -C "$join_source" apply "$normalization_patch"
normalized_caller_blob=$(git -C / hash-object --no-filters \
  "$join_source/V5RelationCallerGenerated.lean")
if [[ "$normalized_caller_blob" != \
    "c9d60c817e396e94011b9afafd68d95bed2b8c15" ]]; then
  echo "unexpected relation-caller import normalization" >&2
  exit 1
fi

echo "COMPILE V5RelationCallerGenerated" | tee -a "$log"
(
  cd "$join_source"
  LEAN_PATH="$olean:$bundle/generated:$formal_overlay:$formal_path:$aeneas_path" \
    "$lean_bin" -j 1 -o "$olean/V5RelationCallerGenerated.olean" \
    V5RelationCallerGenerated.lean >> "$log" 2>&1
)
compile V5RelationAcceptanceSourceProof "$acceptance_proof"
compile V5TranscriptRelationFinalJoin "$final_join_proof"

scan_forbidden_sources() {
  if command -v rg >/dev/null 2>&1; then
    rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' "$@"
  else
    grep -R -n -E \
      '(^|[^[:alnum:]_])(sorry|admit|native_decide|unsafe|ofReduceBool)([^[:alnum:]_]|$)' \
      "$@"
  fi
}

if scan_forbidden_sources "$generated" "$transcript_proof" \
    "$acceptance_proof" "$final_join_proof" \
    "$root/AspisFormal/AspisFormal/V5TranscriptConnection.lean" \
    "$root/AspisFormal/AspisFormal/V5TranscriptSourceAdapter.lean"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if grep -n -E 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in final-join replay" >&2
  exit 1
fi
for theorem in \
    erase_source_relation_exact \
    exact_source_relation \
    generated_helper_matches_exact_source_relation \
    generated_helper_matches_erased_source_relation \
    generated_schedule_and_final_polynomial_gate; do
  if ! grep -Fq "$theorem' depends on axioms:" "$log"; then
    echo "missing #print axioms audit for $theorem" >&2
    exit 1
  fi
done

echo "Lean 4.32 V5 relation transcript/final-gate join replay: PASS"
echo "V5_TRANSCRIPT_FINAL_JOIN_OUT=$out"
echo "axiom audit:"
sed -n "/erase_source_relation_exact' depends on axioms:/,/]/p; \
  /exact_source_relation' depends on axioms:/,/]/p; \
  /generated_helper_matches_exact_source_relation' depends on axioms:/,/]/p; \
  /generated_helper_matches_erased_source_relation' depends on axioms:/,/]/p; \
  /generated_schedule_and_final_polynomial_gate' depends on axioms:/,/]/p" "$log"
echo "log: $log"
