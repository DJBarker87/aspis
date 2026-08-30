#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

for command_name in find git jq wc; do
  command -v "$command_name" >/dev/null || fail "required command is unavailable: $command_name"
done
if command -v sha256sum >/dev/null 2>&1; then
  sha_file() { sha256sum "$1" | awk '{print $1}'; }
  sha_stdin() { sha256sum | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
  sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }
  sha_stdin() { shasum -a 256 | awk '{print $1}'; }
else
  fail "sha256sum or shasum is required"
fi

readonly BUNDLE=$(cd "$(dirname "$0")" && pwd)
readonly ROOT=$(cd "$BUNDLE/../.." && pwd)
readonly MANIFEST="$BUNDLE/manifest.json"
readonly BUNDLE_VERIFY="$ROOT/scripts/v7_txv1_bundle_verify.sh"
[[ -f "$MANIFEST" && -x "$BUNDLE_VERIFY" ]] || fail "release preflight is incomplete"

jq -e '
  .schema == "aspis.v7.one-tx-candidate-preflight.v1" and
  .status == "STACK_SAFE_SOURCE_FROZEN_DUAL_SBF_AND_LOCAL_AGAVE_PENDING" and
  .authorization.build == true and
  .authorization.localDisposableLifecycle == true and
  .authorization.sign == true and .authorization.submit == true and
  .authorization.signAndSubmitScope == "DISPOSABLE_LOCAL_VALIDATOR_ONLY" and
  .authorization.deploy == false and .authorization.mainnet == false and
  .source.commit == "6bc7d3caf181be23a8a6ac7769497c965cd7273d" and
  .source.tree == "aae627375ad1f4f48ac4eae8e0c585c6c0680bab" and
  .source.poolTree == "cd7df911f651f84f408053fd934421aa88c7a9ca" and
  .source.verifierTree == "e7370c020cac1e51ca9e41092dcf6ecbf095bd99" and
  ([.programs[] | select(.name == "aspis-pool")][0] |
    .expectedBytes == 526056 and
    .expectedSha256 == "0bbe441f0e13c2f61e2369674628b06c9d538192514b4e9a92d229479956586d" and
    .referenceArtifactCheckedIn == true) and
  ([.programs[] | select(.name == "aspis-verifier")][0] |
    .expectedBytes == 1812264 and
    .expectedSha256 == "c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47" and
    .referenceArtifactCheckedIn == true) and
  .currentReleaseGate.focusedPlannerMaximumStackOffsetBytes == 2912 and
  .currentReleaseGate.focusedLaneDecoderMaximumStackOffsetBytes == 3024 and
  .currentReleaseGate.maximumAllowedStackOffsetBytes == 4096 and
  .currentReleaseGate.dualLinuxSbfExecuted == false and
  .currentReleaseGate.disposableAgaveLifecycleExecuted == false and
  .txv1Lifecycle.caseBundleIncluded == true and
  .txv1Lifecycle.caseBundlePoolSbfBindingComplete == false and
  .txv1Lifecycle.materializedCaseBundleIncluded == false and
  .txv1Lifecycle.agave42AvailableInRecordedLocalEnvironment == true and
  .txv1Lifecycle.suiteExecutedForThisFreeze == false and
  .currentMeasuredCombinedCase.executed == false
' "$MANIFEST" >/dev/null || fail "manifest is not the exact pending stack-safe release gate"

readonly SOURCE_COMMIT=$(jq -er '.source.commit' "$MANIFEST")
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{commit}")" == "$SOURCE_COMMIT" ]] \
  || fail "frozen source commit is unavailable"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{tree}")" == "$(jq -er '.source.tree' "$MANIFEST")" ]] \
  || fail "frozen source tree differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:Cargo.lock")" == "$(jq -er '.source.cargoLockBlob' "$MANIFEST")" ]] \
  || fail "frozen Cargo.lock blob differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-pool")" == "$(jq -er '.source.poolTree' "$MANIFEST")" ]] \
  || fail "frozen Pool subtree differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-verifier")" == "$(jq -er '.source.verifierTree' "$MANIFEST")" ]] \
  || fail "frozen verifier subtree differs"

while IFS=$'\t' read -r frozen_path expected_sha; do
  [[ "$(git -C "$ROOT" show "$SOURCE_COMMIT:$frozen_path" | sha_stdin)" == "$expected_sha" ]] \
    || fail "source-frozen file differs: $frozen_path"
done < <(jq -r '.sourceFrozenFiles[] | [.path, .sha256] | @tsv' "$MANIFEST")

while IFS=$'\t' read -r program_manifest expected_sha; do
  [[ "$(git -C "$ROOT" show "$SOURCE_COMMIT:$program_manifest" | sha_stdin)" == "$expected_sha" ]] \
    || fail "program manifest differs: $program_manifest"
done < <(jq -r '.programs[] | [.manifest, .manifestSha256] | @tsv' "$MANIFEST")

for evidence_key in \
  '.toolchain.frozenInventory' \
  '.toolchain.offlineCargoCache | {path:.provenancePath,sha256:.provenanceSha256}' \
  '.toolchain.offlineCargoCache | {path:.packagesPath,sha256:.packagesSha256}' \
  '.toolchain.offlineCargoCache | {path:.indexPath,sha256:.indexSha256}' \
  '.toolchain.offlineCargoCache | {path:.sbfProvenancePath,sha256:.sbfProvenanceSha256}' \
  '.toolchain.offlineCargoCache | {path:.sbfPackagesPath,sha256:.sbfPackagesSha256}' \
  '.toolchain.offlineCargoCache | {path:.sbfIndexPath,sha256:.sbfIndexSha256}'; do
  evidence_path=$(jq -er "$evidence_key | .path" "$MANIFEST")
  evidence_sha=$(jq -er "$evidence_key | .sha256" "$MANIFEST")
  [[ -f "$ROOT/$evidence_path" && "$(sha_file "$ROOT/$evidence_path")" == "$evidence_sha" ]] \
    || fail "toolchain/cache evidence differs: $evidence_path"
done
[[ "$(wc -l <"$ROOT/$(jq -er '.toolchain.offlineCargoCache.packagesPath' "$MANIFEST")" | tr -d ' ')" \
    == "$(jq -er '.toolchain.offlineCargoCache.packages' "$MANIFEST")" ]] \
  || fail "host Cargo package inventory count differs"
[[ "$(wc -l <"$ROOT/$(jq -er '.toolchain.offlineCargoCache.sbfPackagesPath' "$MANIFEST")" | tr -d ' ')" \
    == "$(jq -er '.toolchain.offlineCargoCache.sbfPackages' "$MANIFEST")" ]] \
  || fail "SBF Cargo package inventory count differs"

while IFS=$'\t' read -r harness_path expected_sha; do
  [[ -f "$ROOT/$harness_path" && "$(sha_file "$ROOT/$harness_path")" == "$expected_sha" ]] \
    || fail "release-harness file differs: $harness_path"
done < <(jq -r '.releaseHarnessFiles[] | [.path, .sha256] | @tsv' "$MANIFEST")

while IFS=$'\t' read -r program_name artifact expected_bytes expected_sha checked_in; do
  [[ "$checked_in" == "true" && -f "$ROOT/$artifact" ]] \
    || fail "reference artifact is unavailable: $program_name"
  [[ "$(wc -c <"$ROOT/$artifact" | tr -d ' ')" == "$expected_bytes" ]] \
    || fail "reference artifact length differs: $program_name"
  [[ "$(sha_file "$ROOT/$artifact")" == "$expected_sha" ]] \
    || fail "reference artifact hash differs: $program_name"
done < <(jq -r '.programs[] | [.name,.referenceArtifact,.expectedBytes,.expectedSha256,.referenceArtifactCheckedIn] | @tsv' "$MANIFEST")

readonly CASE_BUNDLE="$ROOT/$(jq -er '.txv1Lifecycle.caseBundle' "$MANIFEST")"
readonly OFFLINE_AUDIT="$ROOT/$(jq -er '.txv1Lifecycle.caseBundleOfflineAudit' "$MANIFEST")"
[[ -d "$CASE_BUNDLE" && -f "$OFFLINE_AUDIT" ]] || fail "case template/audit is unavailable"
[[ "$(sha_file "$CASE_BUNDLE/bundle.json")" == "$(jq -er '.txv1Lifecycle.caseBundleSha256' "$MANIFEST")" ]] \
  || fail "case-bundle manifest differs"
[[ "$(sha_file "$CASE_BUNDLE/TEMPLATE-SHA256SUMS")" == "$(jq -er '.txv1Lifecycle.caseBundleInventorySha256' "$MANIFEST")" ]] \
  || fail "case-bundle inventory differs"
[[ "$(sha_file "$OFFLINE_AUDIT")" == "$(jq -er '.txv1Lifecycle.caseBundleOfflineAuditSha256' "$MANIFEST")" ]] \
  || fail "case-bundle offline audit differs"
case_file_count=$(find "$CASE_BUNDLE" -type f | wc -l | tr -d ' ')
case_bytes=$(find "$CASE_BUNDLE" -type f -print0 | xargs -0 wc -c | awk 'END {print $1}')
[[ "$case_file_count" == "$(jq -er '.txv1Lifecycle.caseBundleFiles' "$MANIFEST")" \
    && "$case_bytes" == "$(jq -er '.txv1Lifecycle.caseBundleBytes' "$MANIFEST")" ]] \
  || fail "case-bundle file count or bytes differ"
fresh_audit=$($BUNDLE_VERIFY "$CASE_BUNDLE")
jq -e --argjson fresh "$fresh_audit" --argjson frozen "$(jq . "$OFFLINE_AUDIT")" '$fresh == $frozen' \
  <<<null >/dev/null || fail "fresh case-bundle audit differs from the frozen result"

jq -n \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$(jq -er '.source.tree' "$MANIFEST")" \
  --arg poolTree "$(jq -er '.source.poolTree' "$MANIFEST")" \
  --arg verifierTree "$(jq -er '.source.verifierTree' "$MANIFEST")" \
  --arg poolSha "$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedSha256' "$MANIFEST")" \
  --arg verifierSha "$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedSha256' "$MANIFEST")" \
  --arg caseBundleSha "$(jq -er '.txv1Lifecycle.caseBundleSha256' "$MANIFEST")" '
  {
    schema: "aspis.v7.stack-safe-release-input-audit.v1",
    sourceCommit: $sourceCommit,
    sourceTree: $sourceTree,
    poolTree: $poolTree,
    verifierTree: $verifierTree,
    poolReferenceSha256: $poolSha,
    verifierReferenceSha256: $verifierSha,
    caseBundleSha256: $caseBundleSha,
    exactCaseCount: 11,
    stackOffsetsUnder4096: true,
    dualLinuxSbfPending: true,
    disposableAgaveLifecyclePending: true,
    publicClusterAuthorized: false
  }'
