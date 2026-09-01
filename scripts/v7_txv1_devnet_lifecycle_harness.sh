#!/usr/bin/env bash
set -euo pipefail

readonly REPO_ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly DEFAULT_CONFIG="$REPO_ROOT/config/v7-txv1-devnet-harness-20260901.json"
readonly DISPOSABLE_ACK="I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

usage() {
  cat >&2 <<'USAGE'
usage:
  scripts/v7_txv1_devnet_lifecycle_harness.sh probe \
    <rpc-url> <expected-genesis-hash> <new-evidence-dir> [config.json]

  scripts/v7_txv1_devnet_lifecycle_harness.sh run-disposable \
    <agave-4.2+-bin-dir> <bundle-dir> <new-evidence-dir> \
    I_ACKNOWLEDGE_AUDIT_ONLY_IDENTITIES_AND_DISPOSABLE_FUNDS [config.json]

`probe` is read-only. `run-disposable` is default-off, rejects public RPCs,
uses only an ephemeral validator wallet, and delegates the already frozen
signed/simulated/byte-identical/finalized 11-case corpus. It deliberately does
not claim the missing full-lifecycle cases are complete.
USAGE
  exit 2
}

for command_name in awk curl date git jq mkdir openssl shasum; do
  command -v "$command_name" >/dev/null || fail "missing required command: $command_name"
done

sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }

validate_common() {
  local config=$1 evidence_dir=$2
  [[ -f "$config" ]] || fail "missing config: $config"
  [[ "$evidence_dir" == /* && "$evidence_dir" != "/" ]] \
    || fail "evidence directory must be an explicit absolute non-root path"
  [[ ! -e "$evidence_dir" ]] || fail "refusing to overwrite evidence directory: $evidence_dir"
  jq -e '
    .schema == "aspis.v7.txv1-devnet-harness-config.v1" and
    .mainnetReady == false and
    .feature.id == "txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL" and
    .feature.owner == "Feature111111111111111111111111111111111111" and
    .feature.transactionVersion == 1 and
    .feature.serializedByteCeilingExclusive == 4096 and
    .feature.researchReviewThresholdExclusive == 3500 and
    (.identitySet.auditOnly | type == "boolean") and
    (.identitySet.productionApproved | type == "boolean") and
    (.identitySet.programs | length == 3) and
    (.identitySet.bindingAccounts | length == 2) and
    (.requiredCases | length == 14) and
    (.requiredCases | unique | length == 14)
  ' "$config" >/dev/null || fail "invalid or unsafe harness config"
}

rpc_to_file() {
  local rpc_url=$1 request=$2 output=$3
  curl --fail-with-body --silent --show-error --max-time 30 \
    -H 'content-type: application/json' --data-binary "$request" "$rpc_url" >"$output"
}

probe_cluster() {
  local rpc_url=$1 expected_genesis=$2 evidence_dir=$3 config=$4
  validate_common "$config" "$evidence_dir"
  mkdir -p "$evidence_dir/program-accounts"

  local artifact relative expected_sha
  while IFS=$'\t' read -r relative expected_sha; do
    artifact="$REPO_ROOT/$relative"
    [[ -f "$artifact" ]] || fail "missing frozen binary: $relative"
    [[ "$(sha_file "$artifact")" == "$expected_sha" ]] \
      || fail "frozen binary hash mismatch: $relative"
  done < <(jq -r '.identitySet.programs[] | [.binary, .sha256] | @tsv' "$config")

  rpc_to_file "$rpc_url" '{"jsonrpc":"2.0","id":1,"method":"getHealth"}' \
    "$evidence_dir/get-health.json"
  rpc_to_file "$rpc_url" '{"jsonrpc":"2.0","id":2,"method":"getGenesisHash"}' \
    "$evidence_dir/get-genesis-hash.json"
  rpc_to_file "$rpc_url" '{"jsonrpc":"2.0","id":3,"method":"getVersion"}' \
    "$evidence_dir/get-version.json"
  rpc_to_file "$rpc_url" '{"jsonrpc":"2.0","id":4,"method":"getSlot","params":[{"commitment":"finalized"}]}' \
    "$evidence_dir/get-finalized-slot.json"

  local feature_id feature_owner
  feature_id=$(jq -er '.feature.id' "$config")
  feature_owner=$(jq -er '.feature.owner' "$config")
  rpc_to_file "$rpc_url" \
    "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"getAccountInfo\",\"params\":[\"$feature_id\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
    "$evidence_dir/txv1-feature-account.json"

  jq -e '.result == "ok"' "$evidence_dir/get-health.json" >/dev/null \
    || fail "RPC health gate failed"
  local actual_genesis
  actual_genesis=$(jq -er '.result' "$evidence_dir/get-genesis-hash.json")
  [[ "$actual_genesis" == "$expected_genesis" ]] \
    || fail "genesis hash mismatch: expected $expected_genesis, got $actual_genesis"

  local program name id
  while IFS=$'\t' read -r name id; do
    rpc_to_file "$rpc_url" \
      "{\"jsonrpc\":\"2.0\",\"id\":6,\"method\":\"getAccountInfo\",\"params\":[\"$id\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
      "$evidence_dir/program-accounts/$name.json"
  done < <(jq -r '.identitySet.programs[] | [.name, .id] | @tsv' "$config")
  while IFS=$'\t' read -r name id; do
    rpc_to_file "$rpc_url" \
      "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"getAccountInfo\",\"params\":[\"$id\",{\"encoding\":\"base64\",\"commitment\":\"finalized\"}]}" \
      "$evidence_dir/program-accounts/binding-$name.json"
  done < <(jq -r '.identitySet.bindingAccounts[] | [.name, .id] | @tsv' "$config")

  local feature_active=false feature_present=false activation_slot=null feature_reason
  if jq -e '.result.value != null' "$evidence_dir/txv1-feature-account.json" >/dev/null; then
    feature_present=true
    if jq -e --arg owner "$feature_owner" '
      .result.value.owner == $owner and .result.value.executable == false and
      (.result.value.data[0] | type == "string" and startswith("AQ"))
    ' "$evidence_dir/txv1-feature-account.json" >/dev/null; then
      feature_active=true
      local -a feature_octets
      feature_octets=($(jq -er '.result.value.data[0]' "$evidence_dir/txv1-feature-account.json" \
        | openssl base64 -d -A | od -An -tu1))
      [[ ${#feature_octets[@]} -eq 9 && ${feature_octets[0]} -eq 1 ]] \
        || fail "activated feature account has the wrong canonical data length"
      activation_slot=0
      local byte_index
      for byte_index in {1..8}; do
        activation_slot=$((activation_slot + feature_octets[byte_index] * (1 << (8 * (byte_index - 1)))))
      done
      feature_reason="finalized feature account is present and activated"
    else
      feature_reason="feature account is present but malformed, wrongly owned, or pending"
    fi
  else
    feature_reason="feature account is absent at finalized commitment"
  fi

  local identities_available identity_accounts_valid=true binding_accounts_valid=true
  local remote_binary_hashes_valid=true cli_version=null
  identities_available=$(jq -n \
    --slurpfile pool "$evidence_dir/program-accounts/pool.json" \
    --slurpfile registry "$evidence_dir/program-accounts/registry.json" \
    --slurpfile verifier "$evidence_dir/program-accounts/verifier.json" \
    '[$pool[0],$registry[0],$verifier[0]] | all(.result.value != null)')
  if [[ "$identities_available" == true ]]; then
    while IFS=$'\t' read -r name expected_owner; do
      jq -e --arg owner "$expected_owner" \
        '.result.value != null and .result.value.executable == true and .result.value.owner == $owner' \
        "$evidence_dir/program-accounts/$name.json" >/dev/null \
        || identity_accounts_valid=false
    done < <(jq -r '.identitySet.programs[] | [.name, .loader] | @tsv' "$config")
  else
    identity_accounts_valid=false
    remote_binary_hashes_valid=false
  fi
  while IFS=$'\t' read -r name expected_owner expected_data_sha; do
    local binding_file="$evidence_dir/program-accounts/binding-$name.json"
    if ! jq -e --arg owner "$expected_owner" \
      '.result.value != null and .result.value.executable == false and .result.value.owner == $owner' \
      "$binding_file" >/dev/null; then
      binding_accounts_valid=false
      continue
    fi
    local actual_data_sha
    actual_data_sha=$(jq -er '.result.value.data[0]' "$binding_file" \
      | openssl base64 -d -A | shasum -a 256 | awk '{print $1}')
    [[ "$actual_data_sha" == "$expected_data_sha" ]] || binding_accounts_valid=false
  done < <(jq -r '.identitySet.bindingAccounts[] | [.name, .owner, .dataSha256] | @tsv' "$config")
  if [[ "$identities_available" == true ]]; then
    local solana_cli=${SOLANA_CLI:-}
    if [[ -z "$solana_cli" ]]; then
      solana_cli=$(command -v solana || true)
    fi
    if [[ ! -x "$solana_cli" ]]; then
      remote_binary_hashes_valid=false
    else
      cli_version=$(NO_DNA=1 "$solana_cli" --version | jq -Rs .)
      mkdir -p "$evidence_dir/program-binary-hashes"
      while IFS=$'\t' read -r name id expected_sha; do
        local dumped="$evidence_dir/program-binary-hashes/$name.so"
        if ! NO_DNA=1 "$solana_cli" program dump --url "$rpc_url" "$id" "$dumped" \
          >"$evidence_dir/program-binary-hashes/$name.dump.log" 2>&1; then
          remote_binary_hashes_valid=false
          continue
        fi
        local dumped_sha
        dumped_sha=$(sha_file "$dumped")
        printf '%s  %s\n' "$dumped_sha" "$name.so" \
          >"$evidence_dir/program-binary-hashes/$name.sha256"
        [[ "$dumped_sha" == "$expected_sha" ]] || remote_binary_hashes_valid=false
        rm -f -- "$dumped"
      done < <(jq -r '.identitySet.programs[] | [.name, .id, .sha256] | @tsv' "$config")
    fi
  fi
  local repository_revision repository_dirty=false
  repository_revision=$(git -C "$REPO_ROOT" rev-parse HEAD)
  [[ -z "$(git -C "$REPO_ROOT" status --short)" ]] || repository_dirty=true
  local missing_cases
  missing_cases=$(jq -c '.requiredCases - .availableFrozenCases' "$config")

  jq -n \
    --arg generatedAt "$(date -u +%Y-%m-%dT%H:%M:%SZ)" \
    --arg repositoryRevision "$repository_revision" \
    --argjson repositoryDirty "$repository_dirty" \
    --arg rpcUrl "$rpc_url" --arg genesisHash "$actual_genesis" \
    --arg expectedGenesisHash "$expected_genesis" \
    --arg coreVersion "$(jq -er '.result."solana-core"' "$evidence_dir/get-version.json")" \
    --argjson featureSet "$(jq -er '.result."feature-set"' "$evidence_dir/get-version.json")" \
    --argjson finalizedSlot "$(jq -er '.result' "$evidence_dir/get-finalized-slot.json")" \
    --arg featureId "$feature_id" --arg featureReason "$feature_reason" \
    --argjson featurePresent "$feature_present" --argjson featureActive "$feature_active" \
    --argjson activationSlot "$activation_slot" \
    --argjson identitiesAvailable "$identities_available" \
    --argjson identityAccountsValid "$identity_accounts_valid" \
    --argjson bindingAccountsValid "$binding_accounts_valid" \
    --argjson remoteBinaryHashesValid "$remote_binary_hashes_valid" \
    --argjson cliVersion "$cli_version" \
    --argjson missingCases "$missing_cases" --slurpfile config "$config" '
    {
      schema: "aspis.v7.txv1-devnet-lifecycle-evidence.v1",
      generatedAt: $generatedAt,
      repository: {revision: $repositoryRevision, dirty: $repositoryDirty},
      status: (if ($featureActive | not) then "BLOCKED BY FEATURE/IDENTITY/ARTIFACT"
               elif (($identitiesAvailable and $identityAccountsValid and $bindingAccountsValid and $remoteBinaryHashesValid) | not) then "BLOCKED BY FEATURE/IDENTITY/ARTIFACT"
               elif $config[0].identitySet.auditOnly or ($config[0].identitySet.productionApproved | not) then "BLOCKED BY FEATURE/IDENTITY/ARTIFACT"
               elif ($missingCases | length) > 0 then "BLOCKED BY FEATURE/IDENTITY/ARTIFACT"
               else "PUBLIC DEVNET FEATURE ACTIVE" end),
      cluster: {
        rpcUrl: $rpcUrl, genesisHash: $genesisHash,
        expectedGenesisHash: $expectedGenesisHash, identityVerified: true,
        coreVersion: $coreVersion, featureSet: $featureSet, finalizedSlot: $finalizedSlot
      },
      feature: {
        id: $featureId, accountPresent: $featurePresent,
        activeAtFinalizedCommitment: $featureActive, activationSlot: $activationSlot,
        reason: $featureReason
      },
      identities: {
        set: $config[0].identitySet, allProgramAccountsPresent: $identitiesAvailable,
        programOwnersLoadersExecutableValid: $identityAccountsValid,
        registryProfileReleasePolicyDataHashesValid: $bindingAccountsValid,
        localBinaryHashesValid: true,
        remoteBinaryHashesValid: $remoteBinaryHashesValid,
        acceptedForPublicExecution:
          ($identitiesAvailable and $identityAccountsValid and $bindingAccountsValid and
           $remoteBinaryHashesValid and ($config[0].identitySet.auditOnly | not) and
           $config[0].identitySet.productionApproved)
      },
      toolchain: {solanaCliVersion: $cliVersion},
      transaction: {
        version: 1, byteCeilingExclusive: 4096, researchReviewThresholdExclusive: 3500,
        serializedBytes: null, signedWireSha256: null, exactBytesSimulatedAndSubmitted: false
      },
      lifecycle: {
        requiredCases: $config[0].requiredCases,
        availableFrozenCases: $config[0].availableFrozenCases,
        missingCases: $missingCases,
        finalizedComplete: false
      },
      measurements: {computeUnits: null, signatures: [], slots: [], beforeAfterAccountHashes: []},
      invariants: [
        {name:"authoritative-cluster-identity", pass:true},
        {name:"txv1-feature-finalized-active", pass:$featureActive},
        {name:"production-identities", pass:false},
        {name:"complete-required-case-artifacts", pass:(($missingCases | length) == 0)},
        {name:"finalized-combined-lifecycle", pass:false}
      ],
      artifactBlockers: $config[0].artifactBlockers,
      mutationAttempted: false, signed: false, submitted: false, deployed: false,
      realFundsUsed: false, mainnetReady: false
    }' >"$evidence_dir/evidence.json"

  if [[ "$feature_active" != true ]]; then
    echo "BLOCKED BY FEATURE/IDENTITY/ARTIFACT: $feature_reason" >&2
    return 3
  fi
  if [[ "$identities_available" != true || "$identity_accounts_valid" != true \
      || "$binding_accounts_valid" != true || "$remote_binary_hashes_valid" != true \
      || "$(jq -er '.identitySet.auditOnly' "$config")" == true \
      || "$(jq -er '.identitySet.productionApproved' "$config")" != true \
      || "$missing_cases" != "[]" ]]; then
    echo "BLOCKED BY FEATURE/IDENTITY/ARTIFACT: identity or case artifacts incomplete" >&2
    return 4
  fi
  echo "PUBLIC DEVNET FEATURE ACTIVE: $evidence_dir/evidence.json"
}

run_disposable() {
  local agave_bin=$1 bundle_dir=$2 evidence_dir=$3 ack=$4 config=$5
  validate_common "$config" "$evidence_dir"
  [[ "$ack" == "$DISPOSABLE_ACK" ]] || fail "missing exact disposable-test acknowledgement"
  [[ "$(jq -er '.identitySet.auditOnly' "$config")" == true ]] \
    || fail "run-disposable requires an explicitly audit-only identity set"
  local runner="$REPO_ROOT/scripts/v7_registry_v2_disposable_agave_finalize.sh"
  [[ -x "$runner" ]] || fail "missing frozen disposable runner"
  mkdir -p "$evidence_dir"
  "$runner" "$agave_bin" "$bundle_dir" "$evidence_dir/frozen-11-case"
  local allow_over_3500=${ASPIS_TXV1_RESEARCH_OVER_3500:-}
  if [[ "$allow_over_3500" != "I_ACKNOWLEDGE_RESEARCH_TX_OVER_3500_BYTES" ]]; then
    jq -e '.cases | all(.packetBytes < 3500)' \
      "$evidence_dir/frozen-11-case/suite.json" >/dev/null \
      || fail "transaction exceeds 3,500 bytes without the exact research override"
  fi
  jq -n --slurpfile suite "$evidence_dir/frozen-11-case/suite.json" --slurpfile config "$config" \
    --arg revision "$(git -C "$REPO_ROOT" rev-parse HEAD)" '
    {
      schema:"aspis.v7.txv1-devnet-lifecycle-evidence.v1",
      repository:{revision:$revision}, status:"HARNESS TESTED LOCALLY",
      cluster:{kind:"disposable-agave", featureActiveAtGenesis:true},
      frozenSubset:$suite[0],
      lifecycle:{
        requiredCases:$config[0].requiredCases,
        availableFrozenCases:$config[0].availableFrozenCases,
        missingCases:($config[0].requiredCases - $config[0].availableFrozenCases),
        finalizedComplete:false,
        provisioning:"genesis fixtures; proof upload and Pool init/deposit not executed"
      },
      invariants:[
        {name:"frozen-11-case-finalized-subset",pass:true},
        {name:"complete-required-case-artifacts",pass:false},
        {name:"proof-upload-observed",pass:false},
        {name:"pool-init-deposit-observed",pass:false},
        {name:"finalized-combined-lifecycle",pass:false}
      ],
      mutationAttempted:true, realFundsUsed:false, publicClusterUsed:false,
      deployed:false, mainnetReady:false
    }' >"$evidence_dir/evidence.json"
  echo "HARNESS TESTED LOCALLY: $evidence_dir/evidence.json"
}

[[ $# -ge 1 ]] || usage
case $1 in
  probe)
    [[ $# -eq 4 || $# -eq 5 ]] || usage
    probe_cluster "$2" "$3" "$4" "${5:-$DEFAULT_CONFIG}"
    ;;
  run-disposable)
    [[ $# -eq 5 || $# -eq 6 ]] || usage
    run_disposable "$2" "$3" "$4" "$5" "${6:-$DEFAULT_CONFIG}"
    ;;
  *) usage ;;
esac
