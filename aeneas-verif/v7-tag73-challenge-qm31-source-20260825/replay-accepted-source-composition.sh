#!/usr/bin/env bash
set -euo pipefail

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
repo_root=${REPO_ROOT:-$(cd "$script_dir/../.." && pwd)}

readonly expected_bridge_sha=1e45009650690933eca7e3b4e5535632ce1f9023510dbfd637f1145e10722732
readonly expected_compact_types_sha=f7f643caaee597aa0bf1b8147396fcef80ff1e8073db43c0db631deec5b8dd30
readonly expected_compact_funs_sha=73fefb4eee847570c37c230277f9c8526646a19a41522061580f41348dc1878e
readonly expected_replacement_source_sha=c4c47dd007dee4a7de345838a551f766895204c5aed1239869cecf24f911067b
readonly expected_certificate_source_sha=8e6185fa55fb9d7117e613f0182e1e9d08b627019d2f155636c94120bdc80016
readonly expected_sampler_log_sha=6e59f9423a7fd305104074d7765f7ef429303f09249cdddf4002fab4696789d1
readonly expected_replacement_types_olean_sha=3a9457f6ee4ae1fdb3d2df753a5fbff5f9710cdd1a139fd47a0e72a7e35fb69d
readonly expected_replacement_external_olean_sha=a694c5c7a4baf1d4ebe361f09b11dea6a5a9f7b9bf6dc246d59ccd420ec01ab8
readonly expected_compact_funs_olean_sha=b2e68e137d3d83ccc742ae6b60bc4f564cc74839dbcc6e75889b60dfba123859
readonly expected_certificate_olean_sha=4a2f55cfa80e58d6c5cc12edeee03b402dc367b6b8ce3986a2784139f3618385
readonly expected_source_types_olean_sha=f9af15c6d08e8f80ff6dc28c0a892ee53ea7228979d3dc0b511ec05e85ea822b
readonly expected_source_external_olean_sha=7eb0830fe074626238ae856ad213650fd414ae25caa8d6f48e405e3fd89ce30e
readonly expected_source_funs_olean_sha=6f7471183849bc4e48f720bc0c02d2bf20e2ba55981c858b10008b3ead0ebc9e
readonly expected_aeneas_lean_sources_sha=b98335b2ce64c0e72730159fc86987dd456b8d8dace6dd7a2cd9f5ccf5946433
readonly expected_aeneas_lean_oleans_sha=cd6d2204d071615a7c386af875908c375f94a1f4bec456df49cc7b37fce11ef5
readonly expected_aspis_manifest_sha=65c23cce5c1bab2ba00affdff53fe52b67388cf2491c7f8ec68c1c2977dd7c10

compact_bundle=${COMPACT_BUNDLE_ROOT:-$repo_root/aeneas-verif/v7-tag73-compact-semantic-source-20260825/generated-full/V7CompactSemanticChallengeOpaqueNoDedup}
bridge_source=${COMPACT_SOURCE_BRIDGE:-$repo_root/aeneas-verif/v7-tag73-compact-semantic-source-20260825/proof/V7CompactSemanticSourceBridge.lean}
replacement_root=${REPLACEMENT_OLEAN_ROOT:-/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/replacement-olean}
compact_root=${COMPACT_OLEAN_ROOT:-/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/root-olean}
certificate_root=${CERTIFICATE_OLEAN_ROOT:-/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/proof-olean}
source_olean_root=${SOURCE_OLEAN_ROOT:-/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/olean}
aeneas_lean_root=${AENEAS_LEAN_ROOT:-/home/dombarker/project-offloads/ZK-v5-formal/aeneas-lean}
aspis_formal_root=${ASPIS_FORMAL_ROOT:-/home/dombarker/project-offloads/aspis-v7-accepted-semantic-relation-20260825-agent/AspisFormal}
lean_bin=${LEAN_BIN:-/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean}
export PATH="${LEAN_LAUNCHER_DIR:-/home/dombarker/.elan/bin}:${RUST_BIN_DIR:-/home/dombarker/.cargo/bin}:$PATH"
export LEAN_NUM_THREADS=1

echo "$expected_bridge_sha  $bridge_source" | sha256sum -c -
echo "$expected_compact_types_sha  $compact_bundle/Types.lean" | sha256sum -c -
echo "$expected_compact_funs_sha  $compact_bundle/Funs.lean" | sha256sum -c -
echo "$expected_replacement_source_sha  $script_dir/replacement/V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.lean" |
  sha256sum -c -
echo "$expected_certificate_source_sha  $script_dir/proof/V7Tag73ChallengeQm31SourceCertificate.lean" |
  sha256sum -c -
echo "$expected_sampler_log_sha  $script_dir/logs/nuc-replay-final8.log" |
  sha256sum -c -
echo "$expected_replacement_types_olean_sha  $replacement_root/V7CompactSemanticChallengeOpaqueNoDedup/Types.olean" |
  sha256sum -c -
echo "$expected_replacement_external_olean_sha  $replacement_root/V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.olean" |
  sha256sum -c -
echo "$expected_compact_funs_olean_sha  $compact_root/V7CompactSemanticChallengeOpaqueNoDedup/Funs.olean" |
  sha256sum -c -
echo "$expected_certificate_olean_sha  $certificate_root/V7Tag73ChallengeQm31SourceCertificate.olean" |
  sha256sum -c -
echo "$expected_source_types_olean_sha  $source_olean_root/V7Tag73ChallengeQm31/Types.olean" |
  sha256sum -c -
echo "$expected_source_external_olean_sha  $source_olean_root/V7Tag73ChallengeQm31/FunsExternal.olean" |
  sha256sum -c -
echo "$expected_source_funs_olean_sha  $source_olean_root/V7Tag73ChallengeQm31/Funs.olean" |
  sha256sum -c -
echo "$expected_aspis_manifest_sha  $aspis_formal_root/lake-manifest.json" |
  sha256sum -c -

actual_aeneas_lean_sources_sha=$(
  cd "$aeneas_lean_root"
  find Aeneas -type f -name '*.lean' -print0 |
    sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}'
)
[[ "$actual_aeneas_lean_sources_sha" == "$expected_aeneas_lean_sources_sha" ]]
actual_aeneas_lean_oleans_sha=$(
  cd "$aeneas_lean_root"
  find .lake/build/lib/lean/Aeneas -type f -name '*.olean' -print0 |
    sort -z | xargs -0 sha256sum | sha256sum | awk '{print $1}'
)
[[ "$actual_aeneas_lean_oleans_sha" == "$expected_aeneas_lean_oleans_sha" ]]
case $("$lean_bin" --version) in
  'Lean (version 4.32.0,'*) ;;
  *) echo 'expected Lean 4.32.0' >&2; exit 1 ;;
esac

if rg -n '\b(sorry|admit|axiom|native_decide)\b' "$bridge_source"; then
  echo 'forbidden proof escape found in production source bridge' >&2
  exit 1
fi
if [[ ${PREFLIGHT_ONLY:-0} == 1 ]]; then
  echo 'V7 challenge_qm31 accepted-source composition preflight: PASS'
  exit 0
fi

composition_tmp=$(mktemp -d)
trap 'rm -rf -- "$composition_tmp"' EXIT
checked="$composition_tmp/checked"
bridge_olean="$composition_tmp/olean"
dependency_root="$composition_tmp/dependency-olean"
dependency_namespace="$dependency_root/V7CompactSemanticChallengeOpaqueNoDedup"
bridge_log="$composition_tmp/V7CompactSemanticSourceBridge.axioms.log"
mkdir -p "$checked" "$bridge_olean" "$dependency_namespace"
cp "$replacement_root/V7CompactSemanticChallengeOpaqueNoDedup/Types.olean" \
  "$dependency_namespace/Types.olean"
cp "$replacement_root/V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.olean" \
  "$dependency_namespace/FunsExternal.olean"
cp "$compact_root/V7CompactSemanticChallengeOpaqueNoDedup/Funs.olean" \
  "$dependency_namespace/Funs.olean"
echo "$expected_replacement_types_olean_sha  $dependency_namespace/Types.olean" |
  sha256sum -c -
echo "$expected_replacement_external_olean_sha  $dependency_namespace/FunsExternal.olean" |
  sha256sum -c -
echo "$expected_compact_funs_olean_sha  $dependency_namespace/Funs.olean" |
  sha256sum -c -
cp "$bridge_source" "$checked/V7CompactSemanticSourceBridge.lean"
[[ $(sha256sum "$checked/V7CompactSemanticSourceBridge.lean" | awk '{print $1}') == \
  "$expected_bridge_sha" ]]

aspis_lean_path=$(cd "$aspis_formal_root" && lake env printenv LEAN_PATH)
export LEAN_PATH="$bridge_olean:$dependency_root:$source_olean_root:$certificate_root:$aeneas_lean_root/.lake/build/lib/lean:$aspis_lean_path"
(
  cd "$checked"
  "$lean_bin" -o "$bridge_olean/V7CompactSemanticSourceBridge.olean" \
    V7CompactSemanticSourceBridge.lean
) 2>&1 | tee "$bridge_log"
[[ -f "$bridge_olean/V7CompactSemanticSourceBridge.olean" ]]

perl "$script_dir/normalization/assert-accepted-source-axioms.pl" \
  "$bridge_log" "$script_dir/logs/nuc-replay-final8.log"

if [[ -n ${COMPOSITION_DIAGNOSTICS_DIR:-} ]]; then
  mkdir -p "$COMPOSITION_DIAGNOSTICS_DIR"
  cp "$bridge_log" \
    "$COMPOSITION_DIAGNOSTICS_DIR/V7CompactSemanticSourceBridge.axioms.log"
  sha256sum "$bridge_olean/V7CompactSemanticSourceBridge.olean" > \
    "$COMPOSITION_DIAGNOSTICS_DIR/V7CompactSemanticSourceBridge.olean.sha256"
fi

echo 'V7 challenge_qm31 accepted-source composition replay: PASS'
