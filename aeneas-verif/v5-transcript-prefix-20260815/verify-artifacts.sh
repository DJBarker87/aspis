#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly artifact_dir="${V5_PREFIX_ARTIFACT_DIR:?set V5_PREFIX_ARTIFACT_DIR}"
readonly archived_commit="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly archived_blob="1083179fccac7efda7340b82a91c79ba1946513c"
readonly transformed_blob="6bdb5f1cd54610b4b3fc3ebb6c493a7c40b6e746"
readonly source_file="programs/aspis-verifier/src/v5_cu_probe.rs"
readonly source_patch="$bundle/deployed-prefix-initialized-transcript.patch"
readonly normalized_lean="$root/AspisFormal/AspisFormal/V5TranscriptPrefixNormalizedGenerated.lean"
readonly bridge_lean="$root/AspisFormal/AspisFormal/V5TranscriptPrefixExtractionBridge.lean"
readonly normalization_checker="$bundle/check-normalized-success-path.py"

check_sha256() {
  local expected=$1
  local target_file=$2
  [[ -f "$target_file" ]]
  [[ "$(shasum -a 256 "$target_file" | awk '{print $1}')" == "$expected" ]]
}

[[ "$(git -C "$root" rev-parse "$archived_commit:$source_file")" == \
  "$archived_blob" ]]

check_sha256 \
  a84b4d559241d87fd9cd0937ed9ff486b1f55237baf62b463dad8095161cfaad \
  "$source_patch"
check_sha256 \
  68e51358b1f40381583e3c269533cc1f604360050b96546b5d5b1ffafa8b8df0 \
  "$normalized_lean"
check_sha256 \
  1230fa590ece3652a13905308aa66659d45a4ec54e081425aec4c4aeab5aeb9a \
  "$bridge_lean"
check_sha256 \
  8e5271c9cb69bde8ade9f7018cdde0061278c97fa90db8b73193414e79ac1343 \
  "$normalization_checker"

check_sha256 \
  0d465ce9291cc57b6fd6ec149abdd8c2d3474a9244ff4336e99de4f9dcd6b319 \
  "$artifact_dir/prefix-core.llbc"
check_sha256 \
  791309c868758730462991aa5a5fce1cce4d4b1379e9b27314881e4b09a298ed \
  "$artifact_dir/prefix-core.llbc.txt"
check_sha256 \
  19564142fdddd93b41674554d42df8a0486763b5ce765682b83103408b13b063 \
  "$artifact_dir/core-raw/Funs.lean"
check_sha256 \
  278ea857c1197308bf22e05d3461f13837cdc200d11625b6f8d3d14396c651fa \
  "$artifact_dir/core-raw/Types.lean"
check_sha256 \
  b6664a379775e572749f96c00f7749442123dae63a9565551b203bc1cb8527d1 \
  "$artifact_dir/core-raw/FunsExternal_Template.lean"
check_sha256 \
  aa82991203f4ee597a6773d805942a0f2fd622cd2782715ae3a11bd73eca57eb \
  "$artifact_dir/core-raw/TypesExternal_Template.lean"

audit_dir=$(mktemp -d /private/tmp/aspis-prefix-audit.XXXXXX)
cleanup() {
  git -C "$root" worktree remove --force "$audit_dir" >/dev/null 2>&1 || true
}
trap cleanup EXIT

git -C "$root" worktree add --detach "$audit_dir" "$archived_commit" \
  >/dev/null
git -C "$audit_dir" apply --unidiff-zero --check "$source_patch"
git -C "$audit_dir" apply --unidiff-zero "$source_patch"
[[ "$(git -C "$audit_dir" hash-object "$source_file")" == \
  "$transformed_blob" ]]
git -C "$audit_dir" diff --check

rg -F 'verify_v5_wire_prefix_from_initialized_transcript' \
  "$artifact_dir/prefix-core.llbc.txt" >/dev/null
rg -F 'def v5_cu_probe.verify_v5_wire_prefix_from_initialized_transcript' \
  "$artifact_dir/core-raw/Funs.lean" >/dev/null

python3 "$normalization_checker" \
  "$artifact_dir/core-raw/Funs.lean" "$normalized_lean"

echo "V5 transcript-prefix artifact, transformation, and normalization: PASS"
