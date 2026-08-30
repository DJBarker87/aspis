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
  .status == "STACK_SAFE_DUAL_SBF_AND_LOCAL_AGAVE_GREEN" and
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
  .currentReleaseGate.dualLinuxSbfExecuted == true and
  .currentReleaseGate.disposableAgaveLifecycleExecuted == true and
  .currentReleaseGate.allElevenCasesFinalized == true and
  .currentReleaseGate.allNegativeCasesRolledBackExactly == true and
  .currentReleaseGate.allHonestCasesUnder1300000Cu == true and
  .currentReleaseGate.publicClusterUsed == false and
  .txv1Lifecycle.caseBundleIncluded == true and
  .txv1Lifecycle.caseBundlePoolSbfBindingComplete == true and
  .txv1Lifecycle.materializedCaseBundleIncluded == true and
  .txv1Lifecycle.agave42AvailableInRecordedLocalEnvironment == true and
  .txv1Lifecycle.suiteExecutedForThisFreeze == true and
  .txv1Lifecycle.allCasesFinalized == true and
  .txv1Lifecycle.allNegativeCasesRolledBackExactly == true and
  .txv1Lifecycle.allHonestCasesMatchFrozenProgramState == true and
  .txv1Lifecycle.programStateComparisonExcludesRuntimeMetadata == ["rentEpoch"] and
  .txv1Lifecycle.publicDevnetSubmissionAuthorized == false and
  .txv1Lifecycle.publicClusterUsed == false and
  .currentMeasuredCombinedCase.executed == true and
  .currentMeasuredCombinedCase.computeUnits == 1217607 and
  .currentMeasuredCombinedCase.transactionBytes == 1031 and
  .currentMeasuredCombinedCase.computeUnitHeadroom == 82393 and
  .currentMeasuredCombinedCase.transactionByteHeadroom == 3065
' "$MANIFEST" >/dev/null || fail "manifest is not the exact green stack-safe release gate"

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

readonly MATERIALIZED_BUNDLE="$ROOT/$(jq -er '.txv1Lifecycle.materializedCaseBundle' "$MANIFEST")"
readonly MATERIALIZED_AUDIT="$ROOT/$(jq -er '.txv1Lifecycle.materializedCaseBundleOfflineAudit' "$MANIFEST")"
readonly SBF_RECORD="$ROOT/$(jq -er '.currentReleaseGate.reproducibleSbfRecord' "$MANIFEST")"
readonly SUITE="$ROOT/$(jq -er '.txv1Lifecycle.suite' "$MANIFEST")"
readonly RELEASE_EVIDENCE="$ROOT/$(jq -er '.currentReleaseGate.releaseEvidence' "$MANIFEST")"
readonly EVIDENCE_INVENTORY="$ROOT/$(jq -er '.currentReleaseGate.evidenceInventory' "$MANIFEST")"
[[ -d "$MATERIALIZED_BUNDLE" && -f "$MATERIALIZED_AUDIT" && -f "$SBF_RECORD" \
    && -f "$SUITE" && -f "$RELEASE_EVIDENCE" && -f "$EVIDENCE_INVENTORY" ]] \
  || fail "green release evidence is incomplete"
[[ "$(sha_file "$MATERIALIZED_BUNDLE/bundle.json")" \
      == "$(jq -er '.txv1Lifecycle.materializedCaseBundleSha256' "$MANIFEST")" ]] \
  || fail "materialized bundle manifest differs"
[[ "$(sha_file "$MATERIALIZED_BUNDLE/TEMPLATE-SHA256SUMS")" \
      == "$(jq -er '.txv1Lifecycle.materializedCaseBundleInventorySha256' "$MANIFEST")" ]] \
  || fail "materialized bundle inventory differs"
[[ "$(sha_file "$MATERIALIZED_AUDIT")" \
      == "$(jq -er '.txv1Lifecycle.materializedCaseBundleOfflineAuditSha256' "$MANIFEST")" ]] \
  || fail "materialized bundle audit differs"
fresh_materialized_audit=$($BUNDLE_VERIFY "$MATERIALIZED_BUNDLE" --materialized)
jq -e --argjson fresh "$fresh_materialized_audit" \
  --argjson frozen "$(jq . "$MATERIALIZED_AUDIT")" '$fresh == $frozen' \
  <<<null >/dev/null || fail "fresh materialized-bundle audit differs"

[[ "$(sha_file "$SBF_RECORD")" == "$(jq -er '.currentReleaseGate.reproducibleSbfRecordSha256' "$MANIFEST")" ]] \
  || fail "reproducible SBF record differs"
jq -e \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$(jq -er '.source.tree' "$MANIFEST")" \
  --arg poolSha "$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedSha256' "$MANIFEST")" \
  --arg verifierSha "$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedSha256' "$MANIFEST")" '
  .schema == "aspis.v7.one-tx-reproducible-sbf.v2" and
  .source.commit == $sourceCommit and .source.tree == $sourceTree and
  .source.independentCopies == 2 and .source.archivesByteIdentical == true and
  .programs.pool.sha256 == $poolSha and .programs.pool.bytes == 526056 and
  .programs.pool.buildsByteIdentical == true and .programs.pool.stackGate.passed == true and
  .programs.pool.stackGate.plannerMaximumObservedOffsetBytes == 2912 and
  .programs.pool.stackGate.laneDecoderMaximumObservedOffsetBytes == 3024 and
  .programs.verifier.sha256 == $verifierSha and .programs.verifier.bytes == 1812264 and
  .programs.verifier.buildsByteIdentical == true and
  .builder.offlineCargoCacheVerifiedBeforeAndAfter == true and
  .builder.offlineSbfCargoCacheVerifiedBeforeAndAfter == true and
  .builder.memoryMaxBytes <= 12884901888 and .builder.memorySwapMaxBytes == 0
' "$SBF_RECORD" >/dev/null || fail "reproducible SBF record did not close"

[[ "$(sha_file "$SUITE")" == "$(jq -er '.txv1Lifecycle.suiteSha256' "$MANIFEST")" ]] \
  || fail "finalized Agave suite differs"
jq -e \
  --arg poolSha "$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedSha256' "$MANIFEST")" \
  --arg verifierSha "$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedSha256' "$MANIFEST")" \
  --arg bundleSha "$(jq -er '.txv1Lifecycle.materializedCaseBundleSha256' "$MANIFEST")" '
  def base64_bytes:
    . as $encoded |
    ((($encoded | length) * 3 / 4) -
      (if ($encoded | endswith("==")) then 2 elif ($encoded | endswith("=")) then 1 else 0 end));
  ([.cases[] | {key: .case, value: {bytes: .packetBytes, cu: .landedUnitsConsumed}}] |
    from_entries) as $measured |
  .schema == "aspis.v7.disposable-agave-txv1-finalized-suite.v2" and
  .poolSbfSha256 == $poolSha and .verifierSbfSha256 == $verifierSha and
  .bundleSha256 == $bundleSha and (.cases | length) == 11 and
  .allCasesSigned and .allCasesSubmitted and .allCasesFinalized and
  .allPacketsUnder4096 and .allLandedComputeUnder1300000 and
  .allNegativeCasesRolledBack and .allHonestCasesMatchFrozenProgramState and
  .allHonestRuntimeMetadataValid and
  .programStateComparisonExcludesRuntimeMetadata == ["rentEpoch"] and
  (.cases | all(.simulationUnitsConsumed == .landedUnitsConsumed)) and
  (.cases | map(select(.expectedOutcome == "success")) |
    all((.transactionResponse.result.meta.returnData.data[0] | base64_bytes) == 792)) and
  $measured["transfer-same-page"] == {bytes: 833, cu: 1157102} and
  $measured["transfer-rollover"] == {bytes: 866, cu: 1206015} and
  $measured["withdrawal-same-page"] == {bytes: 998, cu: 1148696} and
  $measured["withdrawal-rollover"] == {bytes: 1031, cu: 1217607} and
  $measured["stale-selected-lane-rejection"] == {bytes: 833, cu: 67809} and
  $measured["replay-nullifier-rejection"] == {bytes: 833, cu: 23666} and
  $measured["wrong-checkpoint-rejection"] == {bytes: 833, cu: 15587} and
  $measured["wrong-registry-release-rejection"] == {bytes: 833, cu: 39727} and
  $measured["malformed-proof-rejection"] == {bytes: 833, cu: 30837} and
  $measured["mutated-proof-rejection"] == {bytes: 833, cu: 974231} and
  $measured["failed-withdrawal-cpi-rollback"] == {bytes: 998, cu: 1147481} and
  (.publicClusterUsed | not) and (.deployed | not)
' "$SUITE" >/dev/null || fail "finalized Agave suite did not close"

while IFS= read -r case_name; do
  case_file="$(dirname "$SUITE")/$case_name.json"
  [[ -f "$case_file" ]] || fail "committed finalized case is missing: $case_name"
  jq -e --arg case "$case_name" --slurpfile standalone "$case_file" \
    '.cases[] | select(.case == $case) | . == $standalone[0]' "$SUITE" >/dev/null \
    || fail "standalone finalized case differs from suite: $case_name"
done < <(jq -r '.txv1Lifecycle.requiredCases[]' "$MANIFEST")

[[ "$(sha_file "$RELEASE_EVIDENCE")" == "$(jq -er '.currentReleaseGate.releaseEvidenceSha256' "$MANIFEST")" ]] \
  || fail "release-evidence summary differs"
jq -e '
  .schema == "aspis.v7.one-tx-stack-safe-local-release-evidence.v1" and
  .reproducibleSbf.dualBuildEvidenceValid and
  .finalizedLifecycle.allCasesFinalized and
  .finalizedLifecycle.allNegativeCasesRolledBackExactly and
  .finalizedLifecycle.allHonestCasesMatchFrozenProgramState and
  (.finalizedLifecycle.cases | length) == 11 and
  (.finalizedLifecycle.cases | all(.simulationEqualsLandedCompute)) and
  (.scope.localReleaseEvidenceComplete == true) and
  (.scope.publicClusterUsed | not) and (.scope.programDeployed | not)
' "$RELEASE_EVIDENCE" >/dev/null || fail "release-evidence summary did not close"

[[ "$(sha_file "$EVIDENCE_INVENTORY")" == "$(jq -er '.currentReleaseGate.evidenceInventorySha256' "$MANIFEST")" ]] \
  || fail "release-evidence inventory differs"
while read -r expected relative_path; do
  [[ -n "$expected" && -n "$relative_path" ]] \
    || fail "malformed release-evidence inventory entry"
  inventory_file="$(dirname "$EVIDENCE_INVENTORY")/$relative_path"
  [[ -f "$inventory_file" ]] || fail "release-evidence file is missing: $relative_path"
  [[ "$(sha_file "$inventory_file")" == "$expected" ]] \
    || fail "release-evidence file differs: $relative_path"
done < "$EVIDENCE_INVENTORY"

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
    dualLinuxSbfPassed: true,
    disposableAgaveLifecyclePassed: true,
    worstHonestComputeUnits: 1217607,
    worstHonestTransactionBytes: 1031,
    allNegativeCasesRolledBackExactly: true,
    publicClusterAuthorized: false
  }'
