#!/usr/bin/env bash
set -euo pipefail

# Offline/read-only verification for the operational bundle. This script never
# builds, signs, contacts an RPC, submits, deploys or reruns the lifecycle.

ROOT="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
MANIFEST="$ROOT/release/v7-registry-v2-mainnet-rc1/manifest.json"
STATEMENTS="$ROOT/release/v7-registry-v2-mainnet-rc1/statement-inventory.json"
SUITE="$ROOT/results/v7-registry-v2-release-audit-20260831/agave-finalized-r1/evidence/suite.json"
RUN_AUDIT="$ROOT/results/v7-registry-v2-release-audit-20260831/agave-finalized-r1/run-audit.json"
SBF_AUDIT="$ROOT/results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2/reproducible-sbf-stack-audit.json"
DEVNET_GATE="$ROOT/results/v7-registry-v2-release-audit-20260831/devnet-feature-gate-r2/gate.json"
V5_LIFECYCLE="$ROOT/release/aspis-v5-tag67-mainnet-v1/evidence/mainnet-lifecycle.json"
SOURCE_COMMIT="7179f7c550fe0461f4251dea5268af73876da91d"

fail() {
  printf 'FAIL: %s\n' "$*" >&2
  exit 1
}

require() {
  command -v "$1" >/dev/null 2>&1 || fail "required read-only tool absent: $1"
}

sha256_file() {
  shasum -a 256 "$1" | awk '{print $1}'
}

expect_file() {
  local relative="$1" expected_bytes="$2" expected_sha="$3"
  local path="$ROOT/$relative"
  [[ -f "$path" ]] || fail "missing $relative"
  [[ "$(wc -c < "$path" | tr -d ' ')" == "$expected_bytes" ]] \
    || fail "byte length differs: $relative"
  [[ "$(sha256_file "$path")" == "$expected_sha" ]] \
    || fail "SHA-256 differs: $relative"
}

expect_git_object() {
  local object="$1" expected_bytes="$2" expected_sha="$3"
  git -C "$ROOT" cat-file -e "$object^{blob}" 2>/dev/null \
    || fail "missing Git blob $object"
  [[ "$(git -C "$ROOT" cat-file -s "$object")" == "$expected_bytes" ]] \
    || fail "Git blob length differs: $object"
  [[ "$(git -C "$ROOT" cat-file blob "$object" | shasum -a 256 | awk '{print $1}')" == "$expected_sha" ]] \
    || fail "Git blob SHA-256 differs: $object"
}

require git
require jq
require shasum
require awk

jq -e . "$MANIFEST" >/dev/null
jq -e . "$STATEMENTS" >/dev/null

jq -e '
  .releaseDecision == "NO_GO" and
  (.mainnetReady | not) and
  (.identityGate.pass | not) and
  .runtime.allCasesFinalized and
  .runtime.successCases == 4 and
  .runtime.negativeCases == 7 and
  .runtime.allNegativeProtectedAccountRollbacksExact and
  .runtime.worstHonestComputeUnits == 1218654 and
  .runtime.largestPacketBytes == 1031 and
  .publicDevnet.status == "INACTIVE" and
  (.publicDevnet.lifecycleAttempted | not) and
  ([.blockers[] | select(.severity == "P0" and .status != "CLOSED")] | length >= 1) and
  ([.productionIdentitySelectionsRequired[] | select(. == "UNSELECTED")] | length >= 1)
' "$MANIFEST" >/dev/null || fail "manifest fail-closed release gates differ"

[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{tree}")" == \
  "72d8ccd295994277bcb5f9df922c2a1483ac0443" ]] \
  || fail "runtime source tree differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-pool")" == \
  "0bebca6b10c61e1d97949da10e6b4901d5117fa0" ]] || fail "Pool source tree differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-verifier")" == \
  "0b9627c523ac47682f3c987abd68ae2027ac5eb2" ]] || fail "verifier source tree differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-registry")" == \
  "50edc0c660f12c68baa6298f8f01e3422ea8b70b" ]] || fail "Registry source tree differs"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:crates/aspis-pool-wallet-v1")" == \
  "7e6e50c4dcae05527ded1b72de0afc5b09cd8fec" ]] || fail "wallet source tree differs"

expect_git_object 8d2cee1604e60153dad98c0ef6826e995729f46a 116375 a1d2fc87435e98734f74a0fb1f070f1eaa5e5fe19266967092a7ea7849f8a91d
expect_git_object 9d9b34951afec6d34172da726c3d711bd51d7861 90511 19414236323c8f038a86e3b1acc6e0a6b87e55ffa6cb5db0e558a47b97613922
expect_git_object 0c7483ebce8e97005e028b63ffad05cbea788ecb 3377 1f3f06d55e891dfcdfb5777380762d7595c109559b12f164d96001c6ddb2d7c5
expect_git_object 1948e590ff154aa1942dcd0828eb76f6a76923c0 61056 becc01f162f23cd9b4a7fd3780be5a441c9b7265f3078282244cc938da63a16c
expect_git_object f3b234ad0a048b8e0960169568ebe783429bad7a 45394 c416304a9edb85208c50a68e0307c5db5cb701d12cee9c3022195135a67abb0b

expect_file results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2/frozen-sbf/aspis_pool.so 534608 0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6
expect_file results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2/frozen-sbf/aspis_verifier.so 1819480 97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d
expect_file results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2/frozen-sbf/aspis_registry.so 189824 0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b
expect_file release/v7-registry-v2-mainnet-rc1/README.md 2733 805d728248e67cab4b28b1b839b473309a028d3bd3e9c51c535d39db0a71e63d
expect_file release/v7-registry-v2-mainnet-rc1/runbook.md 7568 426d3411c6af2de94569753ae58270f039ebbd65f1aafc677f02f7dc62d4fb13
expect_file docs/research/v7-registry-v2-mainnet-readiness-20260901.md 9115 b5161a0d75948e56bf6d41ee0e0fa54f04bca508a7edd2c280f4d0da1dabed4d
expect_file docs/research/v7-registry-v2-mainnet-readiness-20260901.html 9960 169fddd9e14438304b7e4d59b9cede6d2e4ce48f2aad4cf0fe7174da16a833a6
expect_file release/v7-registry-v2-mainnet-rc1/statement-inventory.json 5058 57c642a9298dc8f02561ac7cb57a3e919360d5dde00fe970200662a00cc952f3
expect_file results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/bin/inventory_registry_v2_rc.rs 11711 3e7b94ed7cbe63cbfeee816317c4b7f0c9bb25cb359d406d60387fd2a8b72915
expect_file results/v7-registry-v2-release-audit-20260831/agave-finalized-r1/evidence/suite.json 22941 2772c65a6ae68a7fa66790b1451e905c1df2e61afdef76e2443254fd02b464e8
expect_file results/v7-registry-v2-release-audit-20260831/agave-finalized-r1/run-audit.json 1467 6cd2bd19975f4df2c790190aa8d453ae549bcecc78f8726296c681b3b066ca54
expect_file results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2/reproducible-sbf-stack-audit.json 4443 8ebfb298a3081feccc268ca823662f52205d38435450d369cca15357c0ea157b
expect_file results/v7-registry-v2-release-audit-20260831/devnet-feature-gate-r2/gate.json 1682 0e9e8d9ead3b6de093d0d5c5b3d7ca070ab4401627e3b37a926d1f79ba6ee75e
expect_file release/aspis-v5-tag67-mainnet-v1/evidence/mainnet-lifecycle.json 7002 8cf9057173903e98763ba5485d88291b7564cf6464b9e651e8b52696f6c9a1e3

jq -e '
  .allBuildsByteIdentical and
  .allArtifactsMatchFrozenRegistryV2Evidence and
  .allStackGatesPassed and
  ([.programs[] | .buildsByteIdentical and .stackGatePassed and (.maximumObservedStackAccessBytes <= .stackLimitBytes)] | all)
' "$SBF_AUDIT" >/dev/null || fail "dual-SBF/stack gate differs"

jq -e '
  .cases | length == 11 and
  ([.[] | select(.expectedOutcome == "success")] | length == 4) and
  ([.[] | select(.expectedOutcome == "failure")] | length == 7) and
  ([.[] | .signed and .submitted and .finalized and .sameSignedBytesSimulatedAndSubmitted and (.simulationUnitsConsumed == .landedUnitsConsumed)] | all) and
  ([.[] | select(.expectedOutcome == "success") | .landedError == null and .protectedStateChangedOnSuccess] | all) and
  ([.[] | select(.expectedOutcome == "failure") | (.landedError != null) and .protectedStateRollbackPreserved] | all)
' "$SUITE" >/dev/null || fail "signed/finalized suite invariants differ"

jq -e '
  [
    ["transfer-same-page", 833, 1161348],
    ["transfer-rollover", 866, 1207062],
    ["withdrawal-same-page", 998, 1152942],
    ["withdrawal-rollover", 1031, 1218654],
    ["strict-proof-mutation-rejection", 833, 975278],
    ["wrong-registry-release-rejection", 833, 36573],
    ["stale-selected-lane-rejection", 833, 72055],
    ["replay-nullifier-rejection", 833, 23671],
    ["malformed-result-rejection", 833, 47002],
    ["mutated-result-rejection", 833, 50039],
    ["failed-withdrawal-cpi-rollback", 998, 1151707]
  ] as $expected |
  ([.cases[] | [.case, .packetBytes, .landedUnitsConsumed]] == $expected)
' "$SUITE" >/dev/null || fail "exact packet/CU inventory differs"

jq -e '
  .schema == "aspis.v7.registry-v2-rc-transient-statement-inventory.v1" and
  .bundleSha256 == "1d27eed3e3022172170c351e70f409ed8cdbd83e755c9147a1478c0932d5321d" and
  .readOnly and (.executed | not) and (.signed | not) and (.submitted | not) and
  (.cases | length == 4) and
  ([.cases[].request.bytes] | all(. == 320)) and
  ([.cases[].statement.bytes] | all(. == 1880)) and
  ([.cases[].result.bytes] | all(. == 792))
' "$STATEMENTS" >/dev/null || fail "statement/proof inventory differs"

jq -e '
  .classification == "FAIL_CLOSED_PUBLIC_DEVNET_TXV1_NOT_ACTIVE" and
  (.txv1.activeAtFinalizedCommitment | not) and
  .txv1.featureAccountAtFinalizedCommitment == null and
  (.signed | not) and (.submitted | not) and (.deployed | not) and (.pass | not)
' "$DEVNET_GATE" >/dev/null || fail "public-devnet gate differs"

jq -e '
  .identities.program == "7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue" and
  .identities.programdata == "cdRqe7MGCEJ2Z6iZfWuXtuymRiAhXtyfDgT47sKZr69" and
  .transactions.programdata_close.finalized_slot == 435019804 and
  .transactions.programdata_close.programdata_post_lamports == 0 and
  .transactions.programdata_close.program_account_unchanged and
  .independent_public_rpc_observation.programdata_absent
' "$V5_LIFECYCLE" >/dev/null || fail "historical verifier identity closure evidence differs"

jq -e '.pass and .bundleSha256 == "1d27eed3e3022172170c351e70f409ed8cdbd83e755c9147a1478c0932d5321d"' "$RUN_AUDIT" >/dev/null \
  || fail "finalized-run audit differs"

printf 'PASS: frozen operational evidence is internally consistent\n'
printf 'releaseDecision=NO_GO mainnetReady=false\n'
