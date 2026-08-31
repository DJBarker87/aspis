#!/usr/bin/env bash
set -euo pipefail

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
readonly TOKEN_PROGRAM="TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
readonly SYSTEM_PROGRAM="11111111111111111111111111111111"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

if [[ $# -lt 1 || $# -gt 2 || ( $# -eq 2 && "$2" != "--materialized" ) ]]; then
  echo "usage: $0 <bundle-directory> [--materialized]" >&2
  exit 2
fi

readonly BUNDLE_DIR=$(cd "$1" && pwd)
readonly MATERIALIZED=${2:-}
readonly MANIFEST="$BUNDLE_DIR/bundle.json"
readonly EXPECTED_POOL_SHA256="0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6"
readonly EXPECTED_POOL_BYTES=534608
readonly EXPECTED_VERIFIER_SHA256="97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d"
readonly EXPECTED_VERIFIER_BYTES=1819480
readonly EXPECTED_REGISTRY_SHA256="0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b"
readonly EXPECTED_REGISTRY_BYTES=189824
readonly EXPECTED_RESULT_DOUBLE_SHA256="3693edf83f100ca90229a8aa0406182d71fd56b6480a1fa7366c4caff4ad5c29"
readonly EXPECTED_RESULT_DOUBLE_BYTES=20816

for command_name in cmp find jq openssl sort wc; do
  command -v "$command_name" >/dev/null 2>&1 \
    || fail "required command is unavailable: $command_name"
done
[[ -f "$MANIFEST" && -f "$BUNDLE_DIR/TEMPLATE-SHA256SUMS" ]] \
  || fail "bundle manifest or template checksum inventory is missing"

if command -v sha256sum >/dev/null 2>&1; then
  sha_file() { sha256sum "$1" | awk '{print $1}'; }
  sha_stdin() { sha256sum | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
  sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }
  sha_stdin() { shasum -a 256 | awk '{print $1}'; }
else
  fail "sha256sum or shasum is required"
fi

validate_relative_path() {
  local path=$1
  if [[ -z "$path" || "$path" == /* || "$path" == ".." || "$path" == ../* \
      || "$path" == */../* || "$path" == */.. ]]; then
    fail "bundle path must be nonempty, relative, and contain no parent traversal: $path"
  fi
}

readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-bundle-audit.XXXXXX")
cleanup() {
  case "$WORK_DIR" in
    */aspis-v7-bundle-audit.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
}
trap cleanup EXIT

jq -e \
  --arg verifierSha "$EXPECTED_VERIFIER_SHA256" \
  --argjson verifierBytes "$EXPECTED_VERIFIER_BYTES" \
  --arg poolSha "$EXPECTED_POOL_SHA256" \
  --argjson poolBytes "$EXPECTED_POOL_BYTES" \
  --arg registrySha "$EXPECTED_REGISTRY_SHA256" \
  --argjson registryBytes "$EXPECTED_REGISTRY_BYTES" \
  --arg resultDoubleSha "$EXPECTED_RESULT_DOUBLE_SHA256" \
  --argjson resultDoubleBytes "$EXPECTED_RESULT_DOUBLE_BYTES" '
  .schema == "aspis.v7.registry-v2-disposable-agave-txv1-bundle.v1" and
  .generatorSchema == "aspis.v7.registry-v2-deterministic-agave-bundle-generator.v1" and
  .programSourceCommit == "7179f7c550fe0461f4251dea5268af73876da91d" and
  .programSourceTree == "72d8ccd295994277bcb5f9df922c2a1483ac0443" and
  .poolSourceTree == "0bebca6b10c61e1d97949da10e6b4901d5117fa0" and
  .verifierSourceTree == "0b9627c523ac47682f3c987abd68ae2027ac5eb2" and
  .registrySourceTree == "50edc0c660f12c68baa6298f8f01e3422ea8b70b" and
  (.poolProgram | type == "string" and length > 0) and
  (.verifierProgram | type == "string" and length > 0) and
  (.registryProgram | type == "string" and length > 0) and
  .poolSbf == "sbf/aspis_pool.so" and
  .sbfBindingComplete == true and .executionReady == true and
  .poolSbfSha256 == $poolSha and .poolSbfBytes == $poolBytes and
  .verifierSbf == "sbf/aspis_verifier.so" and
  .verifierSbfSha256 == $verifierSha and
  .verifierSbfBytes == $verifierBytes and
  .registrySbf == "sbf/aspis_registry.so" and
  .registrySbfSha256 == $registrySha and
  .registrySbfBytes == $registryBytes and
  .resultDoubleSbf == "sbf/aspis_pair_forest_result_double.so" and
  .resultDoubleSbfSha256 == $resultDoubleSha and
  .resultDoubleSbfBytes == $resultDoubleBytes and
  .sbfFilesIncludedInTemplate == true and
  .warpSlot == 150 and
  .computeUnitCeiling == 1300000 and
  .transactionByteCeilingExclusive == 4096 and
  .allNegativeCasesRequireRollback == true and
  .signed == false and .submitted == false and .deployed == false and
  (.cases | type == "array" and length == 11)
' "$MANIFEST" >/dev/null || fail "bundle manifest has the wrong frozen schema or bindings"

for case_name in "${REQUIRED_CASES[@]}"; do
  jq -e --arg name "$case_name" \
    '[.cases[] | select(.name == $name)] | length == 1' "$MANIFEST" >/dev/null \
    || fail "bundle omits or duplicates required case: $case_name"
done

# Require the checksum inventory to cover every bundle file exactly.
(
  cd "$BUNDLE_DIR"
  find . -type f ! -name TEMPLATE-SHA256SUMS -print \
    | sed 's#^./##' | sort >"$WORK_DIR/actual-files"
  awk '{print $2}' TEMPLATE-SHA256SUMS | sort >"$WORK_DIR/inventory-files"
  cmp -s "$WORK_DIR/actual-files" "$WORK_DIR/inventory-files" \
    || fail "template checksum inventory does not cover the exact non-SBF file set"
  while read -r expected relative_path; do
    [[ "$(sha_file "$relative_path")" == "$expected" ]] \
      || fail "template file hash differs: $relative_path"
  done <TEMPLATE-SHA256SUMS
)

readonly POOL_PROGRAM=$(jq -er '.poolProgram' "$MANIFEST")
readonly VERIFIER_PROGRAM=$(jq -er '.verifierProgram' "$MANIFEST")
readonly REGISTRY_PROGRAM=$(jq -er '.registryProgram' "$MANIFEST")

for case_name in "${REQUIRED_CASES[@]}"; do
  readonly_case="$WORK_DIR/$case_name.json"
  jq -e --arg name "$case_name" '.cases[] | select(.name == $name)' \
    "$MANIFEST" >"$readonly_case"
  jq -e '
    (.input | type == "string" and length > 0) and
    (.inputSha256 | test("^[0-9a-f]{64}$")) and
    (.expectedOutcome == "success" or .expectedOutcome == "failure") and
    (.expectedLogContains | type == "array" and length > 0 and
      all(type == "string" and length > 0)) and
    (.genesisAccounts | type == "array" and length > 0 and all(
      (.address | type == "string" and length > 0) and
      (.file | type == "string" and length > 0) and
      (.fileSha256 | test("^[0-9a-f]{64}$")) and
      (.loadAtGenesis | type == "boolean")
    )) and
    (.genesisAccountsSha256 | test("^[0-9a-f]{64}$")) and
    (.postStateAccountsSha256 | test("^[0-9a-f]{64}$")) and
    (.programOverrides | type == "array") and
    (.selectedVerifier.file | type == "string" and length > 0) and
    (.selectedVerifier.fileSha256 | test("^[0-9a-f]{64}$")) and
    (.selectedVerifier.fileBytes | type == "number" and . > 0) and
    .selectedVerifier.loader == "upgradeable-none" and
    (.registryV2Fixtures.registrySource | type == "string" and length > 0) and
    (.registryV2Fixtures.registrySha256 | test("^[0-9a-f]{64}$")) and
    .registryV2Fixtures.registryBytes == 256 and
    (.registryV2Fixtures.entrySource | type == "string" and length > 0) and
    (.registryV2Fixtures.entrySha256 | test("^[0-9a-f]{64}$")) and
    .registryV2Fixtures.entryBytes == 320 and
    (.registryV2Fixtures.registryProgramdata | type == "string" and length > 0) and
    (.registryV2Fixtures.verifierProgramdata | type == "string" and length > 0) and
    (.registryV2Fixtures.registryExecutableSha256 | test("^[0-9a-f]{64}$")) and
    (.registryV2Fixtures.selectedVerifierExecutableSha256 | test("^[0-9a-f]{64}$")) and
    (.markerStart.kind == "zero-lamport-system-owned" or
      .markerStart.kind == "consumed-pool-owned") and
    (.markerStart.lamports | type == "number" and . >= 0) and
    (.markerStart.owner | type == "string" and length > 0) and
    (.markerStart.dataBytes | type == "number" and . >= 0) and
    (.rollbackRequired == (.expectedOutcome == "failure")) and
    (if .expectedOutcome == "success" then
      (.expectedSimulationAccountsSha256 | test("^[0-9a-f]{64}$")) and
      (.expectedSimulationAccountsFile | type == "string" and length > 0) and
      (.expectedSimulationAccountsFileSha256 | test("^[0-9a-f]{64}$"))
    else
      .rollbackRequired == true and
      .expectedSimulationAccountsSha256 == null and
      .expectedSimulationAccountsFile == null and
      .expectedSimulationAccountsFileSha256 == null
    end)
  ' "$readonly_case" >/dev/null || fail "case metadata is malformed: $case_name"

  case_input_relative=$(jq -er '.input' "$readonly_case")
  validate_relative_path "$case_input_relative"
  case_input="$BUNDLE_DIR/$case_input_relative"
  [[ -f "$case_input" ]] || fail "missing case input: $case_input_relative"
  [[ "$(sha_file "$case_input")" == "$(jq -er '.inputSha256' "$readonly_case")" ]] \
    || fail "case input hash differs: $case_name"

  jq -e \
    --arg pool "$POOL_PROGRAM" \
    --arg operation "$(jq -er '.name | if startswith("withdrawal") or . == "failed-withdrawal-cpi-rollback" then "withdrawal" else "private-transfer" end' "$readonly_case")" '
      .schema == "aspis.v7.txv1-simulation-input.v1" and
      .poolProgram == $pool and
      .operation == $operation and
      (.historyPath == "same-page" or .historyPath == "rollover") and
      (.feePayer | type == "string" and length > 0) and
      .recentBlockhash == "11111111111111111111111111111111" and
      (.instructionAccounts | type == "array") and
      (.postStateAccounts | type == "array" and length > 0) and
      (.postStateAccounts | unique | length) == (.postStateAccounts | length)
    ' "$case_input" >/dev/null || fail "TxV1 input schema differs: $case_name"

  history=$(jq -er '.historyPath' "$case_input")
  operation=$(jq -er '.operation' "$case_input")
  account_count=$(jq -er '.instructionAccounts | length' "$case_input")
  if [[ "$operation/$history" == "private-transfer/same-page" ]]; then expected_accounts=11
  elif [[ "$operation/$history" == "private-transfer/rollover" ]]; then expected_accounts=12
  elif [[ "$operation/$history" == "withdrawal/same-page" ]]; then expected_accounts=16
  elif [[ "$operation/$history" == "withdrawal/rollover" ]]; then expected_accounts=17
  else fail "unexpected operation/history combination: $case_name"
  fi
  [[ "$account_count" == "$expected_accounts" ]] \
    || fail "instruction account count differs for $case_name"
  if [[ "$history" == "same-page" ]]; then payer_index=5; else payer_index=6; fi
  jq -e \
    --arg payer "$(jq -er '.feePayer' "$case_input")" \
    --arg system "$SYSTEM_PROGRAM" \
    --argjson payerIndex "$payer_index" '
      .instructionAccounts[$payerIndex].pubkey == $payer and
      .instructionAccounts[$payerIndex].writable == true and
      .instructionAccounts[$payerIndex].signer == true and
      .instructionAccounts[$payerIndex + 1].pubkey == $system and
      .instructionAccounts[$payerIndex + 1].writable == false and
      .instructionAccounts[$payerIndex + 1].signer == false and
      ([range(0; (.instructionAccounts | length)) as $index |
        select($index != $payerIndex) |
        .instructionAccounts[$index].signer] | all(. == false))
    ' "$case_input" >/dev/null || fail "marker payer/System Program metas differ: $case_name"
  registry_address=$(jq -er --argjson payerIndex "$payer_index" \
    '.instructionAccounts[$payerIndex + 2].pubkey' "$case_input")
  entry_address=$(jq -er --argjson payerIndex "$payer_index" \
    '.instructionAccounts[$payerIndex + 3].pubkey' "$case_input")
  jq -e \
    --argjson payerIndex "$payer_index" \
    --arg verifier "$VERIFIER_PROGRAM" '
      .instructionAccounts[$payerIndex + 2].writable == false and
      .instructionAccounts[$payerIndex + 3].writable == false and
      .instructionAccounts[$payerIndex + 4].pubkey == $verifier and
      .instructionAccounts[$payerIndex + 4].writable == false
    ' "$case_input" >/dev/null || fail "Registry V2/verifier account metas differ: $case_name"
  registry_account_relative=$(jq -er --arg address "$registry_address" \
    '.genesisAccounts[] | select(.address == $address) | .file' "$readonly_case")
  entry_account_relative=$(jq -er --arg address "$entry_address" \
    '.genesisAccounts[] | select(.address == $address) | .file' "$readonly_case")
  validate_relative_path "$registry_account_relative"
  validate_relative_path "$entry_account_relative"
  registry_account_file="$BUNDLE_DIR/$registry_account_relative"
  entry_account_file="$BUNDLE_DIR/$entry_account_relative"
  jq -e --arg owner "$REGISTRY_PROGRAM" '.owner == $owner and .space == 256' \
    "$registry_account_file" >/dev/null || fail "ASR2 account envelope differs: $case_name"
  jq -e --arg owner "$REGISTRY_PROGRAM" '.owner == $owner and .space == 320' \
    "$entry_account_file" >/dev/null || fail "ASE2 account envelope differs: $case_name"
  jq -r '.data[0]' "$registry_account_file" | openssl base64 -d -A >"$WORK_DIR/$case_name.asr2"
  jq -r '.data[0]' "$entry_account_file" | openssl base64 -d -A >"$WORK_DIR/$case_name.ase2"
  [[ "$(sha_file "$WORK_DIR/$case_name.asr2")" == "$(jq -er '.registryV2Fixtures.registrySha256' "$readonly_case")" \
      && "$(sha_file "$WORK_DIR/$case_name.ase2")" == "$(jq -er '.registryV2Fixtures.entrySha256' "$readonly_case")" ]] \
    || fail "Registry V2 sidecar bytes differ: $case_name"
  [[ "$(LC_ALL=C head -c 4 "$WORK_DIR/$case_name.asr2")" == "ASR2" \
      && "$(LC_ALL=C head -c 4 "$WORK_DIR/$case_name.ase2")" == "ASE2" ]] \
    || fail "Registry V2 sidecar magic differs: $case_name"
  marker_address=$(jq -er --argjson payerIndex "$payer_index" \
    '.instructionAccounts[$payerIndex - 1].pubkey' "$case_input")
  marker_file_relative=$(jq -er --arg marker "$marker_address" \
    '.genesisAccounts[] | select(.address == $marker) | .file' "$readonly_case")
  validate_relative_path "$marker_file_relative"
  marker_file="$BUNDLE_DIR/$marker_file_relative"
  case "$case_name" in
    replay-nullifier-rejection)
      jq -e --arg pool "$POOL_PROGRAM" '
        .markerStart.kind == "consumed-pool-owned" and
        .markerStart.lamports > 0 and .markerStart.owner == $pool and
        .markerStart.dataBytes == 208
      ' "$readonly_case" >/dev/null || fail "consumed marker metadata differs: $case_name"
      ;;
    *)
      jq -e --arg system "$SYSTEM_PROGRAM" '
        .markerStart.kind == "zero-lamport-system-owned" and
        .markerStart.lamports == 0 and .markerStart.owner == $system and
        .markerStart.dataBytes == 0
      ' "$readonly_case" >/dev/null || fail "fresh marker metadata differs: $case_name"
      ;;
  esac

  selected_relative=$(jq -er '.selectedVerifier.file' "$readonly_case")
  validate_relative_path "$selected_relative"
  selected_file="$BUNDLE_DIR/$selected_relative"
  [[ -f "$selected_file" ]] || fail "selected verifier artifact is missing: $case_name"
  [[ "$(sha_file "$selected_file")" == "$(jq -er '.selectedVerifier.fileSha256' "$readonly_case")" \
      && "$(wc -c <"$selected_file" | tr -d ' ')" == "$(jq -er '.selectedVerifier.fileBytes' "$readonly_case")" ]] \
    || fail "selected verifier artifact differs: $case_name"
  [[ "$(jq -er '.registryV2Fixtures.registryExecutableSha256' "$readonly_case")" == "$EXPECTED_REGISTRY_SHA256" ]] \
    || fail "ASR2 executable binding differs: $case_name"
  [[ "$(jq -er '.registryV2Fixtures.selectedVerifierExecutableSha256' "$readonly_case")" \
      == "$(jq -er '.selectedVerifier.fileSha256' "$readonly_case")" ]] \
    || fail "ASE2 selected-verifier executable binding differs: $case_name"
  jq -e \
    --arg owner "$(jq -er '.markerStart.owner' "$readonly_case")" \
    --argjson lamports "$(jq -er '.markerStart.lamports' "$readonly_case")" \
    --argjson bytes "$(jq -er '.markerStart.dataBytes' "$readonly_case")" '
      .owner == $owner and .lamports == $lamports and .space == $bytes
    ' "$marker_file" >/dev/null || fail "marker account image differs from metadata: $case_name"

  jq -r '.instructionDataBase64' "$case_input" \
    | openssl base64 -d -A >"$WORK_DIR/$case_name.asq8"
  [[ "$(wc -c <"$WORK_DIR/$case_name.asq8" | tr -d ' ')" == "320" ]] \
    || fail "ASQ8 is not exactly 320 bytes: $case_name"
  [[ "$(LC_ALL=C head -c 4 "$WORK_DIR/$case_name.asq8")" == "ASQ8" ]] \
    || fail "ASQ8 magic differs: $case_name"

  genesis_canonical_sha=$(jq -cSj '.genesisAccounts' "$readonly_case" | sha_stdin)
  [[ "$genesis_canonical_sha" == "$(jq -er '.genesisAccountsSha256' "$readonly_case")" ]] \
    || fail "canonical genesis-account list hash differs: $case_name"
  post_keys_sha=$(jq -cj '.postStateAccounts' "$case_input" | sha_stdin)
  [[ "$post_keys_sha" == "$(jq -er '.postStateAccountsSha256' "$readonly_case")" ]] \
    || fail "post-state account list hash differs: $case_name"
  jq -e --argjson post "$(jq '.postStateAccounts' "$case_input")" '
    ([.genesisAccounts[].address] | unique | length) == (.genesisAccounts | length) and
    ($post - [.genesisAccounts[].address] | length == 0)
  ' "$readonly_case" >/dev/null || fail "genesis/post-state account coverage differs: $case_name"

  while IFS=$'\t' read -r address relative_path expected_sha; do
    validate_relative_path "$relative_path"
    account_file="$BUNDLE_DIR/$relative_path"
    [[ -f "$account_file" ]] || fail "missing genesis account file: $relative_path"
    [[ "$(sha_file "$account_file")" == "$expected_sha" ]] \
      || fail "genesis account hash differs: $relative_path"
    jq -e '
      (.lamports | type == "number" and . >= 0) and
      (.data | type == "array" and length == 2 and .[1] == "base64") and
      (.owner | type == "string" and length > 0) and
      (.executable | type == "boolean") and
      (.rentEpoch | type == "number") and
      (.space | type == "number" and . >= 0)
    ' "$account_file" >/dev/null || fail "malformed validator account file: $relative_path"
    jq -r '.data[0]' "$account_file" | openssl base64 -d -A >"$WORK_DIR/account.data"
    [[ "$(wc -c <"$WORK_DIR/account.data" | tr -d ' ')" == "$(jq -er '.space' "$account_file")" ]] \
      || fail "account data length differs from space: $relative_path"
    [[ -n "$address" ]] || fail "empty genesis account address"
  done < <(jq -r '.genesisAccounts[] | [.address, .file, .fileSha256] | @tsv' "$readonly_case")
  marker_loaded=$(jq -r --arg marker "$marker_address" \
    '.genesisAccounts[] | select(.address == $marker) | .loadAtGenesis' "$readonly_case")
  marker_lamports=$(jq -er '.markerStart.lamports' "$readonly_case")
  if (( marker_lamports == 0 )); then
    [[ "$marker_loaded" == "false" ]] || fail "zero-lamport marker must model an absent genesis account"
  else
    [[ "$marker_loaded" == "true" ]] || fail "funded marker must be loaded at genesis"
  fi

  if [[ "$(jq -er '.expectedOutcome' "$readonly_case")" == "success" ]]; then
    expected_relative=$(jq -er '.expectedSimulationAccountsFile' "$readonly_case")
    validate_relative_path "$expected_relative"
    expected_file="$BUNDLE_DIR/$expected_relative"
    [[ -f "$expected_file" ]] || fail "missing expected accounts file: $case_name"
    [[ "$(sha_file "$expected_file")" == "$(jq -er '.expectedSimulationAccountsFileSha256' "$readonly_case")" ]] \
      || fail "expected accounts file hash differs: $case_name"
    [[ "$(jq -cSj . "$expected_file" | sha_stdin)" == "$(jq -er '.expectedSimulationAccountsSha256' "$readonly_case")" ]] \
      || fail "expected simulation account hash differs: $case_name"
    [[ "$(jq -er 'length' "$expected_file")" == "$(jq -er '.postStateAccounts | length' "$case_input")" ]] \
      || fail "expected simulation account count differs: $case_name"
    jq -e '.programOverrides | length == 0' "$readonly_case" >/dev/null \
      || fail "honest case must not override a program: $case_name"
    jq -e --arg verifierSha "$EXPECTED_VERIFIER_SHA256" '
      .selectedVerifier.file == "sbf/aspis_verifier.so" and
      .selectedVerifier.fileSha256 == $verifierSha
    ' "$readonly_case" >/dev/null || fail "honest selected-verifier binding differs: $case_name"
  elif [[ "$case_name" == "malformed-result-rejection" \
      || "$case_name" == "mutated-result-rejection" ]]; then
    jq -e \
      --arg verifier "$VERIFIER_PROGRAM" \
      --arg resultSha "$EXPECTED_RESULT_DOUBLE_SHA256" '
      .rollbackRequired == true and
      (.programOverrides | length == 0) and
      .selectedVerifier.file == "sbf/aspis_pair_forest_result_double.so" and
      .selectedVerifier.fileSha256 == $resultSha and
      (.expectedLogContains | any(contains($verifier)))
    ' "$readonly_case" >/dev/null || fail "result-double selection metadata differs: $case_name"
  elif [[ "$case_name" == "failed-withdrawal-cpi-rollback" ]]; then
    jq -e \
      --arg token "$TOKEN_PROGRAM" \
      --arg verifier "$VERIFIER_PROGRAM" \
      --arg verifierSha "$EXPECTED_VERIFIER_SHA256" \
      --arg resultSha "$EXPECTED_RESULT_DOUBLE_SHA256" '
      .rollbackRequired == true and
      .selectedVerifier.file == "sbf/aspis_verifier.so" and
      .selectedVerifier.fileSha256 == $verifierSha and
      (.programOverrides | length == 1) and
      .programOverrides[0].address == $token and
      .programOverrides[0].file == "sbf/aspis_pair_forest_result_double.so" and
      .programOverrides[0].fileSha256 == $resultSha and
      .programOverrides[0].loader == "bpf" and
      (.expectedLogContains | any(contains($verifier))) and
      (.expectedLogContains | any(contains($token)))
    ' "$readonly_case" >/dev/null || fail "failed-CPI test-double metadata differs"
  else
    jq -e '.rollbackRequired == true and (.programOverrides | length == 0)' \
      "$readonly_case" >/dev/null || fail "negative rollback metadata differs: $case_name"
    jq -e --arg verifierSha "$EXPECTED_VERIFIER_SHA256" '
      .selectedVerifier.file == "sbf/aspis_verifier.so" and
      .selectedVerifier.fileSha256 == $verifierSha
    ' "$readonly_case" >/dev/null || fail "production verifier selection differs: $case_name"
  fi
done

jq -e '.sbfBindingComplete == true and .executionReady == true' "$MANIFEST" >/dev/null \
  || fail "replay requires the complete Registry V2 SBF binding"
while IFS=$'\t' read -r relative_path expected_bytes expected_sha; do
  validate_relative_path "$relative_path"
  sbf="$BUNDLE_DIR/$relative_path"
  [[ -f "$sbf" ]] || fail "materialized bundle omits SBF: $relative_path"
  [[ "$(wc -c <"$sbf" | tr -d ' ')" == "$expected_bytes" ]] \
    || fail "materialized SBF length differs: $relative_path"
  [[ "$(sha_file "$sbf")" == "$expected_sha" ]] \
    || fail "materialized SBF hash differs: $relative_path"
done < <(jq -r '[.poolSbf, .poolSbfBytes, .poolSbfSha256],
                   [.verifierSbf, .verifierSbfBytes, .verifierSbfSha256],
                   [.registrySbf, .registrySbfBytes, .registrySbfSha256],
                   [.resultDoubleSbf, .resultDoubleSbfBytes, .resultDoubleSbfSha256] | @tsv' "$MANIFEST")

jq -n \
  --arg schema "aspis.v7.deterministic-agave-bundle-offline-audit.v1" \
  --arg bundleSha256 "$(sha_file "$MANIFEST")" \
  --arg inventorySha256 "$(sha_file "$BUNDLE_DIR/TEMPLATE-SHA256SUMS")" \
  --argjson materialized "$([[ "$MATERIALIZED" == "--materialized" ]] && echo true || echo false)" '
  {
    schema: $schema,
    cases: 11,
    exactRequiredCaseSet: true,
    allNegativeCasesRequireRollback: true,
    hashesAndLengthsMatch: true,
    canonicalAsq8InputsMatch: true,
    deterministicTokenFailureTestDoublePinned: true,
    bundleSha256: $bundleSha256,
    templateInventorySha256: $inventorySha256,
    sbfMaterializedAndMatched: $materialized,
    agaveExecutionPerformed: false,
    signed: false,
    submitted: false,
    deployed: false
  }'
