#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../../.." && pwd -P)"
readonly runtime="$root/aeneas-verif/component-c-runtime-downstream"
readonly canonical="$runtime/relation-table-canonical-current-20260722/generated/normalized/RuntimeEvaluatorCanonicalCurrent20260722"
readonly arithmetic="$root/aeneas-verif/component-b-weight-at/arithmetic-lean432"
readonly b_olean="${COMPONENT_B_ARITHMETIC_OLEAN_DIR:-$root/aeneas-verif/component-b-mask/unified-current-20260722/olean}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:-$root/aeneas-verif/component-a-encoder-eval-residual/capstone/.lake/build/lib/lean}"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"

if [[ -n "${COMPONENT_C_REPLAY_OUT:-}" ]]; then
  out=$COMPONENT_C_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/component-c-public-closure.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/ComponentCRuntimeGenerated" "$out/.done"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$b_olean/CM31MultiplicativeProof.olean" ]]

# Reuse the normalized current extraction, but give every generated crate and
# external helper a private integration namespace.  Aeneas otherwise emits
# namespace-insensitive helper names which collide with Component A/B in the
# combined capstone even though the Rust declarations are independent.
for module in Types FunsExternal Funs; do
  perl -pe '
    s/RuntimeEvaluatorCanonicalCurrent20260722/ComponentCRuntimeGenerated/g;
    s/ComponentCRuntimeCanonicalGenerated/ComponentCRuntimePublicGenerated/g;
  ' "$canonical/$module.lean" > "$out/ComponentCRuntimeGenerated/$module.lean"
done
perl -ne '
  next if /^\@\[discriminant isize\]$/;
  s/discriminant isize, //g;
  print;
' "$out/ComponentCRuntimeGenerated/Types.lean" \
  > "$out/ComponentCRuntimeGenerated/Types.filtered.lean"
mv "$out/ComponentCRuntimeGenerated/Types.filtered.lean" \
  "$out/ComponentCRuntimeGenerated/Types.lean"
perl -pe '
  s/RuntimeEvaluatorCanonicalCurrent20260722/ComponentCRuntimeGenerated/g;
  s/ComponentCRuntimeCanonicalGenerated/ComponentCRuntimePublicGenerated/g;
' "$canonical.lean" > "$out/ComponentCRuntimeGenerated.lean"

# `FunsExternal` closes its crate namespace before emitting library helpers.
# Keep those helpers private as well, then close the namespace at EOF.
perl -0pi -e '
  s/\nend ComponentCRuntimePublicGenerated\n\n\/-- \[core/\n\n\/-- [core/;
  $_ .= "\nend ComponentCRuntimePublicGenerated\n"
    unless /end ComponentCRuntimePublicGenerated\s*\z/;
' "$out/ComponentCRuntimeGenerated/FunsExternal.lean"

# The current schedule extraction is source-authentic.  Its discriminant
# attribute is unused by this proof and is the one remaining global Aeneas
# helper name that would collide in the A/B/C integration environment.
perl -ne '
  next if /^\@\[discriminant isize\]$/;
  s/discriminant isize, //g;
  print;
' "$runtime/replay/runtime_schedule/RuntimeSchedule.lean" > "$out/RuntimeSchedule.lean"

# Copy the exact dependency closure sources, then overlay the current joins
# which retain the stored-OOD identity and current generated result shape.
cp "$runtime"/proof/*.lean "$out/"
cp "$bundle/proof/RuntimeMaintainedRoundSelectors.lean" "$out/"
cp "$bundle/proof/RuntimeReleasedTraceFamiliesSourceJoin.lean" "$out/"
cp "$bundle/proof/RuntimeRelationTableCanonicalityCurrentJoin.lean" "$out/"
cp "$bundle/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean" "$out/"
cp "$bundle/proof/RuntimeRelationRoundControlFlowCurrentJoin.lean" \
  "$out/RuntimeRelationRoundControlFlow.lean"
cp "$bundle/proof/RuntimeRelationSampleStorageCurrentJoin.lean" \
  "$out/RuntimeRelationSampleStorage.lean"

# Point proof bodies at the isolated generated namespace while preserving all
# public theorem namespaces and statements.
for source in "$out"/*.lean; do
  perl -0pi -e '
    s/(^open aspis_prover\s*$)/$1\nopen ComponentCRuntimePublicGenerated/gm;
    s/aspis_prover\.aspis_core\./ComponentCRuntimePublicGenerated.aspis_core./g;
    s/(?<![A-Za-z0-9_.])aspis_core\.field\.P/ComponentCRuntimePublicGenerated.aspis_core.field.P/g;
  ' "$source"
done

cp "$arithmetic/AspisCoreQm31SquareScalars.lean" "$out/"
cp "$arithmetic/QM31MulProof.lean" "$out/"
cp "$arithmetic/QM31SquareScalarsProof.lean" "$out/"

aspis_path=$(cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH)
export LEAN_PATH="$out:$b_olean:$aspis_path:$aeneas_lib"
: > "$log"

compile_direct() {
  local module=$1 source=$2
  echo "COMPILE $module" >> "$log"
  (cd "$out" && "$lean_bin" -j 1 -o "$module.olean" "$source") \
    >> "$log" 2>&1
}

compile_direct AspisCoreQm31SquareScalars AspisCoreQm31SquareScalars.lean
compile_direct QM31MulProof QM31MulProof.lean
compile_direct QM31SquareScalarsProof QM31SquareScalarsProof.lean

compile_module() {
  local module=$1
  local module_path=${module//./\/}
  local source="$out/$module_path.lean"
  local target="$out/$module_path.olean"
  local marker="$out/.done/${module//\//_}"
  [[ -f "$source" ]] || return 0
  [[ -f "$marker" ]] && return 0
  local dependency
  for dependency in $(awk '$1 == "import" { print $2 }' "$source"); do
    compile_module "$dependency"
  done
  echo "COMPILE $module" >> "$log"
  (cd "$out" && "$lean_bin" -j 1 -o "$target" "$source") \
    >> "$log" 2>&1
  touch "$marker"
}

compile_module RuntimeReleasedTraceFamiliesCurrentJoin

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b|set_option max(Heartbeats|RecDepth)' \
    "$out" --glob '*.lean' \
    --glob '!AspisCoreQm31SquareScalars.lean' \
    --glob '!ComponentCRuntimeGenerated/**'; then
  echo "forbidden proof token or raised proof limit" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in Component-C public closure" >&2
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
' "$log"; then
  exit 1
fi

echo "Lean 4.32 Component-C public-output closure replay: PASS"
echo "COMPONENT_C_OLEAN_DIR=$out"
echo "log: $log"
