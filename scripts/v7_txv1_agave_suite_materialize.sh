#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <agave-version-string> <bundle-dir> <evidence-dir>" >&2
  exit 2
fi

readonly VERSION_OUTPUT=$1
readonly BUNDLE_DIR=$2
readonly EVIDENCE_DIR=$3
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

for command in jq shasum; do
  command -v "$command" >/dev/null || {
    echo "missing required command: $command" >&2
    exit 2
  }
done
[[ -f "$BUNDLE_MANIFEST" ]] || {
  echo "missing bundle manifest: $BUNDLE_MANIFEST" >&2
  exit 2
}

for case_name in "${REQUIRED_CASES[@]}"; do
  case_file="$EVIDENCE_DIR/$case_name.case.json"
  [[ -f "$case_file" ]] || {
    echo "missing completed Agave case evidence: $case_file" >&2
    exit 2
  }
  jq -e --arg expected "$case_name" '
    .schema == "aspis.v7.disposable-agave-txv1-simulation-case.v1" and
    .case == $expected and .simulationOnly == true and
    .signed == false and .submitted == false and
    (.packetBytes < 4096) and (.unitsConsumed <= 1300000) and
    .actualLedgerStateUnchanged == true and
    (if .expectedOutcome == "success" then
       .honestProgramStateMatchesFrozenExpected == true
     else
       .negativeFailClosedSimulationObserved == true and
       .negativeRollbackDirectlyObserved == false and
       .failedSimulationReturnedNoAccountSnapshots == true
     end)
  ' "$case_file" >/dev/null || {
    echo "invalid or incomplete Agave case evidence: $case_file" >&2
    exit 2
  }
done

readonly WARP_SLOT=$(jq -er '.warpSlot' "$BUNDLE_MANIFEST")
readonly POOL_SBF_SHA256=$(jq -er '.poolSbfSha256' "$BUNDLE_MANIFEST")
readonly VERIFIER_SBF_SHA256=$(jq -er '.verifierSbfSha256' "$BUNDLE_MANIFEST")
readonly REGISTRY_SBF_SHA256=$(jq -er '.registrySbfSha256' "$BUNDLE_MANIFEST")
readonly RESULT_DOUBLE_SBF_SHA256=$(jq -er '.resultDoubleSbfSha256' "$BUNDLE_MANIFEST")
readonly BUNDLE_SHA256=$(shasum -a 256 "$BUNDLE_MANIFEST" | awk '{print $1}')

jq -s \
  --arg version "$VERSION_OUTPUT" \
  --arg poolSha256 "$POOL_SBF_SHA256" \
  --arg verifierSha256 "$VERIFIER_SBF_SHA256" \
  --arg registrySha256 "$REGISTRY_SBF_SHA256" \
  --arg resultDoubleSha256 "$RESULT_DOUBLE_SBF_SHA256" \
  --arg bundleSha256 "$BUNDLE_SHA256" \
  --argjson warpSlot "$WARP_SLOT" \
  '. as $cases | {
    schema: "aspis.v7.registry-v2-disposable-agave-txv1-simulation-suite.v1",
    agave: $version,
    poolSbfSha256: $poolSha256,
    verifierSbfSha256: $verifierSha256,
    registrySbfSha256: $registrySha256,
    resultDoubleSbfSha256: $resultDoubleSha256,
    bundleSha256: $bundleSha256,
    warpSlot: $warpSlot,
    computeUnitCeiling: 1300000,
    transactionByteCeilingExclusive: 4096,
    signed: false,
    submitted: false,
    publicClusterUsed: false,
    realAgaveSimulationCu: true,
    landedOrFinalizedCu: false,
    allPacketsUnder4096: ($cases | all(.packetBytes < 4096)),
    allSimulationComputeUnder1300000: ($cases | all(.unitsConsumed <= 1300000)),
    allNegativeCasesDirectRollbackObserved:
      ($cases | map(select(.expectedOutcome == "failure")) |
       all(.negativeRollbackDirectlyObserved == true)),
    allNegativeCasesFailClosedInSimulation:
      ($cases | map(select(.expectedOutcome == "failure")) |
       all(.negativeFailClosedSimulationObserved == true)),
    allHonestCasesMatchFrozenProgramState:
      ($cases | map(select(.expectedOutcome == "success")) |
       all(.honestProgramStateMatchesFrozenExpected == true)),
    actualValidatorLedgerUnchangedBySimulation: ($cases | all(.actualLedgerStateUnchanged == true)),
    cases: $cases
  }' "$EVIDENCE_DIR"/*.case.json >"$EVIDENCE_DIR/suite.json"

jq -e '
  (.cases | length) == 11 and
  .allPacketsUnder4096 and .allSimulationComputeUnder1300000 and
  .allNegativeCasesFailClosedInSimulation and .allHonestCasesMatchFrozenProgramState and
  (.allNegativeCasesDirectRollbackObserved | not) and
  .actualValidatorLedgerUnchangedBySimulation and
  (.signed | not) and (.submitted | not) and (.publicClusterUsed | not)
' "$EVIDENCE_DIR/suite.json" >/dev/null

echo "disposable Agave simulation-only suite PASS: $EVIDENCE_DIR/suite.json"
