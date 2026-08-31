#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
  echo "usage: $0 <agave-version-string> <local-test-payer> <bundle-dir> <evidence-dir>" >&2
  exit 2
fi

readonly VERSION_OUTPUT=$1
readonly LOCAL_TEST_PAYER=$2
readonly BUNDLE_DIR=$3
readonly EVIDENCE_DIR=$4
readonly BUNDLE_MANIFEST="$BUNDLE_DIR/bundle.json"
readonly REQUIRED_CASES=(
  transfer-same-page
  transfer-rollover
  withdrawal-same-page
  withdrawal-rollover
  strict-proof-mutation-rejection
  wrong-registry-release-rejection
  stale-selected-lane-rejection
  replay-nullifier-rejection
  malformed-result-rejection
  mutated-result-rejection
  failed-withdrawal-cpi-rollback
)

for command_name in jq shasum; do
  command -v "$command_name" >/dev/null || {
    echo "missing required command: $command_name" >&2
    exit 2
  }
done
[[ -f "$BUNDLE_MANIFEST" ]] || {
  echo "missing bundle manifest: $BUNDLE_MANIFEST" >&2
  exit 2
}

case_files=()
for case_name in "${REQUIRED_CASES[@]}"; do
  case_file="$EVIDENCE_DIR/$case_name.case.json"
  [[ -f "$case_file" ]] || {
    echo "missing finalized Agave case evidence: $case_file" >&2
    exit 2
  }
  jq -e --arg expected "$case_name" --arg payer "$LOCAL_TEST_PAYER" '
    .schema == "aspis.v7.registry-v2-disposable-agave-txv1-finalized-case.v1" and
    .case == $expected and .localTestPayer == $payer and
    .signed == true and .submitted == true and .finalized == true and
    .sameSignedBytesSimulatedAndSubmitted == true and
    .localEphemeralKeyOnly == true and .realFundsUsed == false and
    .publicClusterUsed == false and .deployed == false and
    (.packetBytes < 4096) and (.landedUnitsConsumed <= 1300000) and
    (if .expectedOutcome == "success" then
       .protectedStateChangedOnSuccess == true and
       .simulationMatchesFrozenExpectedState == true and
       .landedStateMatchesFrozenExpectedState == true and
       .returnDataBytes == 792
     else
       .protectedStateRollbackPreserved == true and .landedError != null
     end)
  ' "$case_file" >/dev/null || {
    echo "invalid or incomplete finalized Agave case evidence: $case_file" >&2
    exit 2
  }
  case_files+=("$case_file")
done

readonly WARP_SLOT=$(jq -er '.warpSlot' "$BUNDLE_MANIFEST")
readonly POOL_SBF_SHA256=$(jq -er '.poolSbfSha256' "$BUNDLE_MANIFEST")
readonly VERIFIER_SBF_SHA256=$(jq -er '.verifierSbfSha256' "$BUNDLE_MANIFEST")
readonly REGISTRY_SBF_SHA256=$(jq -er '.registrySbfSha256' "$BUNDLE_MANIFEST")
readonly RESULT_DOUBLE_SBF_SHA256=$(jq -er '.resultDoubleSbfSha256' "$BUNDLE_MANIFEST")
readonly BUNDLE_SHA256=$(shasum -a 256 "$BUNDLE_MANIFEST" | awk '{print $1}')

jq -s \
  --arg version "$VERSION_OUTPUT" --arg localTestPayer "$LOCAL_TEST_PAYER" \
  --arg poolSha256 "$POOL_SBF_SHA256" --arg verifierSha256 "$VERIFIER_SBF_SHA256" \
  --arg registrySha256 "$REGISTRY_SBF_SHA256" \
  --arg resultDoubleSha256 "$RESULT_DOUBLE_SBF_SHA256" \
  --arg bundleSha256 "$BUNDLE_SHA256" --argjson warpSlot "$WARP_SLOT" '
  . as $cases | {
    schema: "aspis.v7.registry-v2-disposable-agave-txv1-finalized-suite.v1",
    agave: $version,
    cluster: "disposable-local-validator",
    localTestPayer: $localTestPayer,
    poolSbfSha256: $poolSha256,
    verifierSbfSha256: $verifierSha256,
    registrySbfSha256: $registrySha256,
    resultDoubleSbfSha256: $resultDoubleSha256,
    bundleSha256: $bundleSha256,
    warpSlot: $warpSlot,
    computeUnitCeiling: 1300000,
    transactionByteCeilingExclusive: 4096,
    cases: $cases,
    realAgaveSimulationCu: true,
    realAgaveLandedCu: true,
    landedOrFinalizedCu: true,
    allCasesSigned: ($cases | all(.signed == true)),
    allCasesSubmitted: ($cases | all(.submitted == true)),
    allCasesFinalized: ($cases | all(.finalized == true)),
    allCasesUsedIdenticalSimulatedAndSubmittedBytes:
      ($cases | all(.sameSignedBytesSimulatedAndSubmitted == true)),
    allPacketsUnder4096: ($cases | all(.packetBytes < 4096)),
    allLandedComputeUnder1300000: ($cases | all(.landedUnitsConsumed <= 1300000)),
    allNegativeCasesDirectRollbackObserved:
      ($cases | map(select(.expectedOutcome == "failure")) |
       all(.protectedStateRollbackPreserved == true)),
    allHonestCasesLandedAndMatchFrozenState:
      ($cases | map(select(.expectedOutcome == "success")) |
       all(.protectedStateChangedOnSuccess == true and
           .landedStateMatchesFrozenExpectedState == true)),
    localEphemeralKeyOnly: true,
    realFundsUsed: false,
    publicClusterUsed: false,
    deployed: false
  }' "${case_files[@]}" >"$EVIDENCE_DIR/suite.json"

jq -e '
  (.cases | length) == 11 and .allCasesSigned and .allCasesSubmitted and
  .allCasesFinalized and .allCasesUsedIdenticalSimulatedAndSubmittedBytes and
  .allPacketsUnder4096 and .allLandedComputeUnder1300000 and
  .allNegativeCasesDirectRollbackObserved and
  .allHonestCasesLandedAndMatchFrozenState and
  .realAgaveLandedCu and .landedOrFinalizedCu and
  .localEphemeralKeyOnly and (.realFundsUsed | not) and
  (.publicClusterUsed | not) and (.deployed | not)
' "$EVIDENCE_DIR/suite.json" >/dev/null || {
  echo "finalized suite summary did not close" >&2
  exit 2
}

echo "disposable Agave finalized suite materialized: $EVIDENCE_DIR/suite.json"
