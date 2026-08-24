#!/usr/bin/env bash
set -euo pipefail

# Rebuild the tracked accepted-path Charon/Aeneas proof closure without using
# any pre-existing object directory under aeneas-verif, /private/tmp, or a
# development NUC.  The target stays configurable for focused diagnostics,
# while the default is the final selected accepted-callback theorem.

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly workspace_dir="$(cd "$verification_dir/.." && pwd -P)"
readonly prepare_aeneas="$script_dir/prepare-aeneas-lean432.sh"

readonly default_target_path="aeneas-verif/v5-result-aware-source-link-20260821/proof/V5AcceptedOneRunDeterministicFinal.lean"
readonly default_target_module="V5AcceptedOneRunDeterministicFinal"
readonly default_target_declaration="AspisV5AcceptedOneRunDeterministicFinal.accepted_composite_security_conclusion_for_any_terminal_evaluator"
readonly target_path="${1:-${ASPIS_ACCEPTED_TARGET_PATH:-$default_target_path}}"
readonly target_module="${2:-${ASPIS_ACCEPTED_TARGET_MODULE:-$default_target_module}}"
readonly target_declaration="${ASPIS_ACCEPTED_AXIOM_DECL:-$default_target_declaration}"
readonly revision="${ASPIS_ACCEPTED_REVISION:-HEAD}"

for command_name in awk git grep jq lake mktemp rg sed sort tar; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 2
  fi
done

if [[ ! -x "$prepare_aeneas" ]]; then
  echo "missing executable Aeneas preparation script: $prepare_aeneas" >&2
  exit 2
fi
if ! git -C "$workspace_dir" cat-file -e "$revision:$target_path" 2>/dev/null; then
  echo "accepted-path target is not tracked at $revision: $target_path" >&2
  exit 2
fi
if [[ ! "$target_module" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]]; then
  echo "invalid Lean target module: $target_module" >&2
  exit 2
fi
if [[ -n "$target_declaration" ]] &&
    [[ ! "$target_declaration" =~ ^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$ ]]; then
  echo "invalid Lean declaration for axiom audit: $target_declaration" >&2
  exit 2
fi

unset LEAN_PATH
unset LEAN_SRC_PATH

if [[ -n "${ASPIS_ACCEPTED_REPLAY_WORK:-}" ]]; then
  work_dir=$ASPIS_ACCEPTED_REPLAY_WORK
  mkdir -p "$work_dir"
  if [[ -n "$(find "$work_dir" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
    echo "ASPIS_ACCEPTED_REPLAY_WORK must be empty: $work_dir" >&2
    exit 2
  fi
else
  work_dir=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/aspis-accepted-lean432.XXXXXX")
fi
readonly work_dir
readonly source_index="$work_dir/tracked-lean-sources.txt"
readonly closure_manifest="$work_dir/accepted-path-closure.tsv"
readonly aeneas_imports="$work_dir/aeneas-imports.txt"
readonly formal_imports="$work_dir/formal-imports.txt"
readonly staged_root="$work_dir/accepted-path"
readonly staged_src="$staged_root/src"
readonly replay_log="$work_dir/accepted-path-replay.log"
readonly aeneas_out="$work_dir/aeneas-lean432"

cleanup() {
  if [[ "${ASPIS_KEEP_ACCEPTED_REPLAY_WORK:-0}" == "1" ]]; then
    echo "ACCEPTED_REPLAY_WORK_DIR=$work_dir"
  else
    rm -rf "$work_dir"
  fi
}
trap cleanup EXIT

git -C "$workspace_dir" ls-tree -r --name-only "$revision" aeneas-verif |
  rg '\.lean$' | LC_ALL=C sort > "$source_index"
: > "$closure_manifest"
: > "$aeneas_imports"
: > "$formal_imports"

# A few historical snapshots intentionally retain the same Lean module name.
# These choices reproduce the exact source family used by the accepted-entry
# bridge.  Every other dependency must resolve uniquely from its module suffix.
module_override() {
  case "$1" in
    AspisCoreCm31Multiplicative)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/AspisCoreCm31Multiplicative.lean" ;;
    AspisCoreFieldReduceU64)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/AspisCoreFieldReduceU64.lean" ;;
    AspisCoreFieldMulNamespaced)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/AspisCoreFieldMulNamespaced.lean" ;;
    AspisCoreHalf)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/AspisCoreHalf.lean" ;;
    CM31ExactModel)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/CM31ExactModel.lean" ;;
    CM31MultiplicativeProof)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/CM31MultiplicativeProof.lean" ;;
    CheckV5FriQueries.FunsExternal)
      echo "aeneas-verif/v5-fri-consumer-exact-20260815/generated/CheckV5FriQueries/FunsExternal.lean" ;;
    ComponentBEvaluatorFieldBridge)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/terminal/ComponentBEvaluatorFieldBridge.lean" ;;
    HalfProof)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/HalfProof.lean" ;;
    HalfShiftCountAdapter)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/HalfShiftCountAdapter.lean" ;;
    M31MulProof)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/M31MulProof.lean" ;;
    M31ReduceU64Proof)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/deps/M31ReduceU64Proof.lean" ;;
    SumProductsArithmetic)
      echo "aeneas-verif/component-b-mask/unified-current-20260722/proof/retarget/SumProductsArithmetic.lean" ;;
    V5MerkleTopologyConstructorModel)
      echo "aeneas-verif/v5-merkle-unchanged-full-20260820/proof/V5MerkleTopologyConstructorModel.lean" ;;
    V5MutableEnumerateSupport)
      echo "aeneas-verif/v5-relation-full-source-20260820/generated-linked/V5MutableEnumerateSupport.lean" ;;
    V5AtomicTerminalPrefixWrapperComplete.Funs)
      echo "aeneas-verif/v5-atomic-terminal-source-20260821/generated/V5AtomicTerminalPrefixWrapperComplete/Funs.lean" ;;
    V5AtomicTerminalPrefixWrapperComplete.Types)
      echo "aeneas-verif/v5-atomic-terminal-source-20260821/generated/V5AtomicTerminalPrefixWrapperComplete/Types.lean" ;;
    V5TranscriptTailUnchangedGenerated.Funs)
      echo "aeneas-verif/v5-transcript-tail-unchanged-20260821/generated/V5TranscriptTailUnchangedGenerated/Funs.lean" ;;
    V5TranscriptTailUnchangedGenerated.Types)
      echo "aeneas-verif/v5-transcript-tail-unchanged-20260821/generated/V5TranscriptTailUnchangedGenerated/Types.lean" ;;
    *) return 1 ;;
  esac
}

resolve_module() {
  local module_name=$1
  local override_path
  local suffix
  local candidates
  local count

  if override_path=$(module_override "$module_name"); then
    if ! grep -Fqx "$override_path" "$source_index"; then
      echo "accepted-path override is not tracked: $module_name -> $override_path" >&2
      exit 1
    fi
    echo "$override_path"
    return
  fi

  suffix="/${module_name//.//}.lean"
  candidates=$(awk -v suffix="$suffix" \
    'length($0) >= length(suffix) && substr($0, length($0)-length(suffix)+1) == suffix { print }' \
    "$source_index")
  count=$(printf '%s\n' "$candidates" | sed '/^$/d' | awk 'END { print NR + 0 }')
  if [[ "$count" -ne 1 ]]; then
    echo "Lean module $module_name resolved to $count tracked sources" >&2
    printf '%s\n' "$candidates" >&2
    echo "add an exact module_override entry before changing the accepted gate" >&2
    exit 1
  fi
  printf '%s\n' "$candidates"
}

enqueue_module() {
  local module_name=$1
  local source_path=$2
  if ! awk -F '\t' -v module="$module_name" '$1 == module { found = 1 } END { exit !found }' \
      "$closure_manifest"; then
    printf '%s\t%s\n' "$module_name" "$source_path" >> "$closure_manifest"
  fi
}

enqueue_module "$target_module" "$target_path"
line_number=1
while :; do
  manifest_line=$(sed -n "${line_number}p" "$closure_manifest")
  if [[ -z "$manifest_line" ]]; then
    break
  fi
  line_number=$((line_number + 1))
  module_name=${manifest_line%%$'\t'*}
  source_path=${manifest_line#*$'\t'}

  while IFS= read -r import_line; do
    for imported_module in $import_line; do
      case "$imported_module" in
        Aeneas|Aeneas.*)
          printf '%s\n' "$imported_module" >> "$aeneas_imports" ;;
        AspisFormal.*)
          printf '%s\n' "$imported_module" >> "$formal_imports" ;;
        Mathlib|Mathlib.*|Lean|Lean.*|Std|Std.*|Init|Init.*|Batteries|Batteries.*)
          ;;
        *)
          dependency_path=$(resolve_module "$imported_module")
          enqueue_module "$imported_module" "$dependency_path" ;;
      esac
    done
  done < <(git -C "$workspace_dir" show "$revision:$source_path" |
    sed -n -E 's/^import[[:space:]]+(.+)$/\1/p')
done

LC_ALL=C sort -u -o "$aeneas_imports" "$aeneas_imports"
LC_ALL=C sort -u -o "$formal_imports" "$formal_imports"

mkdir -p "$staged_src"
while IFS=$'\t' read -r module_name source_path; do
  module_file="$staged_src/${module_name//.//}.lean"
  mkdir -p "$(dirname "$module_file")"
  git -C "$workspace_dir" show "$revision:$source_path" > "$module_file"
done < "$closure_manifest"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' "$staged_src"; then
  echo "accepted-path source closure contains a forbidden proof escape" >&2
  exit 1
fi

readonly closure_count="$(awk 'END { print NR + 0 }' "$closure_manifest")"
if [[ "${ASPIS_ACCEPTED_RESOLVE_ONLY:-0}" == "1" ]]; then
  echo "Accepted-path tracked source resolution: PASS"
  echo "target_path=$target_path"
  echo "target_module=$target_module"
  echo "tracked_closure_modules=$closure_count"
  exit 0
fi

# Build only the AspisFormal modules imported by the tracked accepted-path
# closure.  Building the package's default umbrella here would compile many
# unrelated release ledgers and defeats the purpose of a focused replay gate.
formal_targets=()
while IFS= read -r imported_module; do
  [[ -n "$imported_module" ]] && formal_targets+=("$imported_module")
done < "$formal_imports"
if [[ "${#formal_targets[@]}" -eq 0 ]]; then
  echo "accepted-path closure contains no AspisFormal imports" >&2
  exit 1
fi
(
  cd "$workspace_dir/AspisFormal"
  if [[ "${ASPIS_ACCEPTED_FETCH_MATHLIB_CACHE:-1}" == "1" ]]; then
    lake exe cache get
  fi
  lake build "${formal_targets[@]}"
)
# The two checked manifests pin exactly the same dependency revisions.  Reuse
# this fresh run's formal dependency checkout so the Aeneas build does not
# materialize a second multi-gigabyte mathlib tree.  Aeneas itself is still
# cloned, patched, and compiled from its independently pinned revision.
AENEAS_LEAN432_OUT="$aeneas_out" \
  AENEAS_LEAN432_PACKAGES_SOURCE="$workspace_dir/AspisFormal/.lake/packages" \
  "$prepare_aeneas"
readonly aeneas_backend="$aeneas_out/aeneas/backends/lean"

aeneas_targets=()
while IFS= read -r imported_module; do
  [[ -n "$imported_module" ]] && aeneas_targets+=("$imported_module")
done < "$aeneas_imports"
if [[ "${#aeneas_targets[@]}" -gt 0 ]]; then
  (
    cd "$aeneas_backend"
    lake build "${aeneas_targets[@]}"
  )
fi

audit_module=$target_module
if [[ -n "$target_declaration" ]]; then
  audit_module=AcceptedPathReplayAxiomAudit
  cat > "$staged_src/AcceptedPathReplayAxiomAudit.lean" <<EOF
import $target_module

#print axioms $target_declaration
EOF
fi

# Lake does not discover flat sibling modules merely because the selected root
# imports them.  Register the exact tracked closure as roots, then use path
# requirements for the separately checked Aeneas and AspisFormal packages.
# This makes import scheduling explicit and avoids inheriting a developer's
# LEAN_PATH.
cp "$workspace_dir/AspisFormal/lean-toolchain" "$staged_root/lean-toolchain"
cat > "$staged_root/lakefile.lean" <<EOF
import Lake
open Lake DSL

require «aeneas» from "$aeneas_backend"
require «AspisFormal» from "$workspace_dir/AspisFormal"

package acceptedPathReplay where
  preferReleaseBuild := true

lean_lib AcceptedPathReplay where
  srcDir := "src"
  roots := #[
EOF

root_separator=""
while IFS=$'\t' read -r module_name _source_path; do
  printf '%s    `%s' "$root_separator" "$module_name" >> "$staged_root/lakefile.lean"
  root_separator=$',\n'
done < "$closure_manifest"
if [[ "$audit_module" != "$target_module" ]]; then
  printf '%s    `%s' "$root_separator" "$audit_module" >> "$staged_root/lakefile.lean"
fi
printf '\n  ]\n' >> "$staged_root/lakefile.lean"

# Both path requirements pin the same Git dependency revisions.  The formal
# build above has already validated and built this exact package directory, so
# share it instead of fetching a third copy of mathlib.
mkdir -p "$staged_root/.lake"
ln -s "$workspace_dir/AspisFormal/.lake/packages" "$staged_root/.lake/packages"

(
  cd "$staged_root"
  lake build AcceptedPathReplay 2>&1 | tee "$replay_log"
)

# Match the names only where Lean prints an axiom list.  Some maintained
# modules explicitly state in informational text that they do *not* use
# `Lean.ofReduceBool`; a plain substring scan would reject that evidence.
if rg -n \
    'depends on axioms: \[[^]]*\b(sorryAx|ofReduceBool)\b|^[[:space:]]*(Lean\.)?(sorryAx|ofReduceBool)(,|\])' \
    "$replay_log"; then
  echo "accepted-path theorem dependency output contains a forbidden axiom" >&2
  exit 1
fi
if [[ ! -f "$staged_root/.lake/build/lib/lean/${audit_module//.//}.olean" ]]; then
  echo "accepted-path target object was not produced: $audit_module" >&2
  exit 1
fi

echo "Accepted-path Lean 4.32 replay: PASS"
echo "target_path=$target_path"
echo "target_module=$target_module"
echo "tracked_closure_modules=$closure_count"
echo "aeneas_revision=b59d5188c082f704a418c7cb4e52ad69328002d1"
echo "replay_log=$replay_log"
