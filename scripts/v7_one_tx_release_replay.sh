#!/usr/bin/env bash
set -euo pipefail

readonly ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly PREFLIGHT="$ROOT/release/v7-one-tx-candidate-preflight-v1"
readonly MANIFEST="$PREFLIGHT/manifest.json"
readonly VERIFY_INPUTS="$PREFLIGHT/verify-inputs.sh"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "required command is unavailable: $1"
}

if command -v sha256sum >/dev/null 2>&1; then
  sha_file() { sha256sum "$1" | awk '{print $1}'; }
elif command -v shasum >/dev/null 2>&1; then
  sha_file() { shasum -a 256 "$1" | awk '{print $1}'; }
else
  fail "sha256sum or shasum is required"
fi

usage() {
  cat >&2 <<'USAGE'
usage:
  scripts/v7_one_tx_release_replay.sh check
  scripts/v7_one_tx_release_replay.sh build <new-output-dir>
  scripts/v7_one_tx_release_replay.sh build-and-simulate \
    <new-output-dir> <agave-4.2+-bin-dir> <eleven-case-bundle-dir>

The build modes require Linux x86_64, a cgroup-v2 scope capped at
MemoryHigh<=4 GiB, MemoryMax<=6 GiB and MemorySwapMax=0, and:

  ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<directory containing both
    platform-tools-v1.48/ and solana-active-release/ from the frozen
    91-file toolchain inventory>

No mode signs, submits, deploys, or mutates a public cluster.
USAGE
  exit 2
}

[[ -f "$MANIFEST" && -x "$VERIFY_INPUTS" ]] \
  || fail "V7 preflight bundle is incomplete"

readonly MODE=${1:-}
case "$MODE" in
  check)
    [[ $# -eq 1 ]] || usage
    exec "$VERIFY_INPUTS"
    ;;
  build)
    [[ $# -eq 2 ]] || usage
    ;;
  build-and-simulate)
    [[ $# -eq 4 ]] || usage
    ;;
  *) usage ;;
esac

readonly OUTPUT_DIR=$2
readonly AGAVE_BIN_DIR=${3:-}
readonly CASE_BUNDLE_DIR=${4:-}

for command_name in awk cmp cp find git jq sed sha256sum sort tar uname wc xargs; do
  require_command "$command_name"
done
[[ -x /usr/bin/time ]] || fail "/usr/bin/time is required for release resource evidence"
[[ "$(uname -s)" == "Linux" && "$(uname -m)" == "x86_64" ]] \
  || fail "release SBF reproduction requires Linux x86_64; this host is $(uname -s) $(uname -m)"
[[ ! -e "$OUTPUT_DIR" ]] || fail "refusing to overwrite output path: $OUTPUT_DIR"

readonly TOOLCHAIN_CAPTURE_ROOT=${ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT:-}
[[ -n "$TOOLCHAIN_CAPTURE_ROOT" && -d "$TOOLCHAIN_CAPTURE_ROOT" ]] \
  || fail "ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT must name the frozen toolchain capture"
readonly TOOLCHAIN_PROVENANCE="$ROOT/$(jq -er '.toolchain.frozenInventory.path' "$MANIFEST")"
[[ "$(sha_file "$TOOLCHAIN_PROVENANCE")" == "$(jq -er '.toolchain.frozenInventory.sha256' "$MANIFEST")" ]] \
  || fail "working toolchain inventory differs from the frozen source"
readonly PLATFORM_TOOLS_ROOT="$TOOLCHAIN_CAPTURE_ROOT/platform-tools-v1.48"
readonly SOLANA_ACTIVE_ROOT="$TOOLCHAIN_CAPTURE_ROOT/solana-active-release"
readonly CARGO_BUILD_SBF="$SOLANA_ACTIVE_ROOT/bin/cargo-build-sbf"
readonly SBF_SDK="$SOLANA_ACTIVE_ROOT/bin/platform-tools-sdk/sbf"
[[ -x "$CARGO_BUILD_SBF" ]] || fail "frozen cargo-build-sbf is missing"
[[ -x "$PLATFORM_TOOLS_ROOT/rust/bin/rustc" ]] || fail "frozen platform rustc is missing"
[[ -x "$PLATFORM_TOOLS_ROOT/llvm/bin/clang-19" ]] || fail "frozen platform clang is missing"
[[ -d "$SBF_SDK" ]] || fail "frozen SBF SDK is missing"

readonly CGROUP_RELATIVE=$(awk -F: '$1 == "0" {print $3}' /proc/self/cgroup)
[[ -n "$CGROUP_RELATIVE" ]] || fail "cannot resolve the current cgroup-v2 path"
readonly CGROUP_DIR="/sys/fs/cgroup$CGROUP_RELATIVE"
for control in memory.high memory.max memory.swap.max; do
  [[ -r "$CGROUP_DIR/$control" ]] || fail "cgroup control is unavailable: $control"
done
readonly MEMORY_HIGH=$(<"$CGROUP_DIR/memory.high")
readonly MEMORY_MAX=$(<"$CGROUP_DIR/memory.max")
readonly MEMORY_SWAP_MAX=$(<"$CGROUP_DIR/memory.swap.max")
[[ "$MEMORY_HIGH" =~ ^[0-9]+$ && "$MEMORY_MAX" =~ ^[0-9]+$ && "$MEMORY_SWAP_MAX" =~ ^[0-9]+$ ]] \
  || fail "release build requires finite numeric cgroup memory controls"
readonly REQUIRED_HIGH=$(jq -er '.toolchain.requiredCgroup.memoryHighBytesAtMost' "$MANIFEST")
readonly REQUIRED_MAX=$(jq -er '.toolchain.requiredCgroup.memoryMaxBytesAtMost' "$MANIFEST")
readonly REQUIRED_SWAP=$(jq -er '.toolchain.requiredCgroup.memorySwapMaxBytes' "$MANIFEST")
(( MEMORY_HIGH <= REQUIRED_HIGH )) || fail "MemoryHigh exceeds the frozen 4-GiB limit"
(( MEMORY_MAX <= REQUIRED_MAX )) || fail "MemoryMax exceeds the frozen 6-GiB limit"
(( MEMORY_SWAP_MAX == REQUIRED_SWAP )) || fail "MemorySwapMax must be zero"

mkdir -p "$OUTPUT_DIR"
uname -a >"$OUTPUT_DIR/uname.txt"
[[ -f /etc/os-release ]] || fail "/etc/os-release is required for Linux builder provenance"
cp /etc/os-release "$OUTPUT_DIR/os-release.txt"
readonly WORK_DIR=$(mktemp -d "${TMPDIR:-/tmp}/aspis-v7-one-tx-release.XXXXXX")
cleanup() {
  status=$?
  trap - EXIT
  case "$WORK_DIR" in
    */aspis-v7-one-tx-release.*) rm -rf -- "$WORK_DIR" ;;
    *) echo "refusing to remove unexpected temporary path: $WORK_DIR" >&2 ;;
  esac
  exit "$status"
}
trap cleanup EXIT
trap 'exit 1' HUP INT TERM

"$VERIFY_INPUTS" >"$OUTPUT_DIR/input-audit.json"

echo "[1/5] Verify all frozen toolchain bytes"
expected_cargo_build_sbf_sha=$(jq -er '.toolchain.frozenInventory.cargoBuildSbfSha256' "$MANIFEST")
[[ "$(sha_file "$CARGO_BUILD_SBF")" == "$expected_cargo_build_sbf_sha" ]] \
  || fail "cargo-build-sbf bytes differ from the frozen toolchain"
while IFS=$'\t' read -r relative expected_bytes expected_sha; do
  tool="$TOOLCHAIN_CAPTURE_ROOT/$relative"
  [[ -f "$tool" ]] || fail "frozen toolchain file is missing: $relative"
  actual_bytes=$(wc -c <"$tool" | tr -d ' ')
  [[ "$actual_bytes" == "$expected_bytes" ]] \
    || fail "frozen toolchain file length changed: $relative"
  [[ "$(sha_file "$tool")" == "$expected_sha" ]] \
    || fail "frozen toolchain file hash changed: $relative"
done < <(jq -r '.toolchain_files[] | [.path, .bytes, .sha256] | @tsv' "$TOOLCHAIN_PROVENANCE")

expected_version=$(jq -er '.toolchain.cargoBuildSbfVersion' "$MANIFEST")
actual_version=$($CARGO_BUILD_SBF --version)
[[ "$actual_version" == "$expected_version" ]] \
  || fail "cargo-build-sbf version differs from the frozen toolchain"
platform_rustc_version=$($PLATFORM_TOOLS_ROOT/rust/bin/rustc --version)
[[ "$platform_rustc_version" == "$(jq -er '.toolchain.platformRustc' "$MANIFEST")" ]] \
  || fail "platform rustc version differs from the frozen toolchain"
printf '%s\n' "$actual_version" >"$OUTPUT_DIR/cargo-build-sbf-version.txt"
printf '%s\n' "$platform_rustc_version" >"$OUTPUT_DIR/platform-rustc-version.txt"
"$PLATFORM_TOOLS_ROOT/llvm/bin/clang-19" --version >"$OUTPUT_DIR/platform-clang-version.txt"

echo "[2/5] Export two isolated copies of the exact source commit"
readonly SOURCE_COMMIT=$(jq -er '.source.commit' "$MANIFEST")
readonly SOURCE_DATE_EPOCH=$(git -C "$ROOT" show -s --format=%ct "$SOURCE_COMMIT")
for label in a b; do
  mkdir -p "$WORK_DIR/source-$label"
  git -C "$ROOT" archive "$SOURCE_COMMIT" >"$WORK_DIR/source-$label.tar"
  tar -xf "$WORK_DIR/source-$label.tar" -C "$WORK_DIR/source-$label"
  [[ "$(sha_file "$WORK_DIR/source-$label/Cargo.lock")" == "$(jq -er '.source.cargoLockSha256' "$MANIFEST")" ]] \
    || fail "source-$label Cargo.lock differs from the frozen source"
done
readonly SOURCE_ARCHIVE_A_SHA=$(sha_file "$WORK_DIR/source-a.tar")
readonly SOURCE_ARCHIVE_B_SHA=$(sha_file "$WORK_DIR/source-b.tar")
[[ "$SOURCE_ARCHIVE_A_SHA" == "$SOURCE_ARCHIVE_B_SHA" ]] \
  || fail "independent source archives differ"

build_program() {
  local label=$1
  local program=$2
  local source_dir="$WORK_DIR/source-$label"
  local manifest_path features output_name
  local out_dir="$WORK_DIR/sbf-$label-$program"
  local target_dir="$WORK_DIR/target-$label"
  manifest_path=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .manifest' "$MANIFEST")
  features=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .features' "$MANIFEST")
  output_name=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .output' "$MANIFEST")
  mkdir -p "$out_dir" "$target_dir"
  (
    cd "$source_dir"
    export CARGO_TARGET_DIR="$target_dir"
    export CARGO_BUILD_JOBS=1
    export LANG=C
    export LC_ALL=C
    export NO_DNA=1
    export SOURCE_DATE_EPOCH
    export TZ=UTC
    unset CARGO_ENCODED_RUSTFLAGS RUSTFLAGS
    /usr/bin/time -v -o "$OUTPUT_DIR/build-$label-$program.time" \
      "$CARGO_BUILD_SBF" \
      --manifest-path "$manifest_path" \
      --no-default-features \
      --features "$features" \
      --arch v0 \
      --offline \
      --skip-tools-install \
      --tools-version v1.48 \
      --sbf-sdk "$SBF_SDK" \
      --sbf-out-dir "$out_dir" \
      -- \
      --locked
  ) >"$OUTPUT_DIR/build-$label-$program.log" 2>&1
  [[ -f "$out_dir/$output_name" ]] || fail "build $label omitted $output_name"
}

echo "[3/5] Build Pool and verifier in both isolated source copies"
for label in a b; do
  build_program "$label" aspis-pool
  build_program "$label" aspis-verifier
done

echo "[4/5] Require A/B equality and the frozen measured-candidate hashes"
mkdir -p "$OUTPUT_DIR/sbf"
build_records='[]'
for program in aspis-pool aspis-verifier; do
  output_name=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .output' "$MANIFEST")
  expected_sha=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .expectedSha256' "$MANIFEST")
  expected_bytes=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .expectedBytes' "$MANIFEST")
  artifact_a="$WORK_DIR/sbf-a-$program/$output_name"
  artifact_b="$WORK_DIR/sbf-b-$program/$output_name"
  cmp -s "$artifact_a" "$artifact_b" || fail "$program A/B SBFs are not byte-identical"
  [[ "$(sha_file "$artifact_a")" == "$expected_sha" ]] \
    || fail "$program SBF does not match the frozen measured candidate hash"
  [[ "$(wc -c <"$artifact_a" | tr -d ' ')" == "$expected_bytes" ]] \
    || fail "$program SBF does not match the frozen measured candidate length"
  cp "$artifact_a" "$OUTPUT_DIR/sbf/$output_name"
  for label in a b; do
    time_file="$OUTPUT_DIR/build-$label-$program.time"
    log_file="$OUTPUT_DIR/build-$label-$program.log"
    maximum_rss_kib=$(awk -F: '/Maximum resident set size \(kbytes\)/ {gsub(/[[:space:]]/, "", $2); print $2}' "$time_file")
    elapsed=$(sed -n 's/^[[:space:]]*Elapsed (wall clock) time (h:mm:ss or m:ss):[[:space:]]*//p' "$time_file")
    [[ "$maximum_rss_kib" =~ ^[0-9]+$ && -n "$elapsed" ]] \
      || fail "cannot parse resource evidence for build $label $program"
    build_records=$(jq -c \
      --argjson prior "$build_records" \
      --arg copy "$label" \
      --arg program "$program" \
      --arg elapsed "$elapsed" \
      --arg logSha256 "$(sha_file "$log_file")" \
      --arg timeSha256 "$(sha_file "$time_file")" \
      --argjson maximumResidentSetKiB "$maximum_rss_kib" \
      '$prior + [{copy:$copy, program:$program, elapsed:$elapsed,
        maximumResidentSetKiB:$maximumResidentSetKiB,
        logSha256:$logSha256, timeSha256:$timeSha256}]' <<<null)
  done
done

jq -n \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$(jq -er '.source.tree' "$MANIFEST")" \
  --argjson sourceDateEpoch "$SOURCE_DATE_EPOCH" \
  --arg sourceArchiveASha256 "$SOURCE_ARCHIVE_A_SHA" \
  --arg sourceArchiveBSha256 "$SOURCE_ARCHIVE_B_SHA" \
  --arg toolchainInventorySha256 "$(jq -er '.toolchain.frozenInventory.sha256' "$MANIFEST")" \
  --arg cargoBuildSbfSha256 "$expected_cargo_build_sbf_sha" \
  --arg cargoBuildSbfVersion "$actual_version" \
  --arg uname "$(<"$OUTPUT_DIR/uname.txt")" \
  --arg osReleaseSha256 "$(sha_file "$OUTPUT_DIR/os-release.txt")" \
  --arg poolSha256 "$(sha_file "$OUTPUT_DIR/sbf/aspis_pool.so")" \
  --arg verifierSha256 "$(sha_file "$OUTPUT_DIR/sbf/aspis_verifier.so")" \
  --argjson builds "$build_records" \
  --argjson poolBytes "$(wc -c <"$OUTPUT_DIR/sbf/aspis_pool.so" | tr -d ' ')" \
  --argjson verifierBytes "$(wc -c <"$OUTPUT_DIR/sbf/aspis_verifier.so" | tr -d ' ')" \
  --arg cgroup "$CGROUP_RELATIVE" \
  --argjson memoryHigh "$MEMORY_HIGH" \
  --argjson memoryMax "$MEMORY_MAX" \
  --argjson memorySwapMax "$MEMORY_SWAP_MAX" '
  {
    schema: "aspis.v7.one-tx-reproducible-sbf.v1",
    source: {
      commit: $sourceCommit,
      tree: $sourceTree,
      sourceDateEpoch: $sourceDateEpoch,
      independentCopies: 2,
      archiveASha256: $sourceArchiveASha256,
      archiveBSha256: $sourceArchiveBSha256,
      archivesByteIdentical: ($sourceArchiveASha256 == $sourceArchiveBSha256)
    },
    builder: {
      host: "Linux x86_64",
      containerImage: null,
      toolchainInventorySha256: $toolchainInventorySha256,
      cargoBuildSbfSha256: $cargoBuildSbfSha256,
      cargoBuildSbfVersion: $cargoBuildSbfVersion,
      uname: $uname,
      osReleaseSha256: $osReleaseSha256,
      cgroup: $cgroup,
      memoryHighBytes: $memoryHigh,
      memoryMaxBytes: $memoryMax,
      memorySwapMaxBytes: $memorySwapMax
    },
    builds: $builds,
    programs: {
      pool: {bytes: $poolBytes, sha256: $poolSha256, buildsByteIdentical: true, matchesMeasuredCandidate: true},
      verifier: {bytes: $verifierBytes, sha256: $verifierSha256, buildsByteIdentical: true, matchesMeasuredCandidate: true}
    },
    signed: false,
    submitted: false,
    deployed: false
  }' >"$OUTPUT_DIR/reproducible-sbf.json"

suite_status="UNAVAILABLE_NOT_REQUESTED"
suite_sha256=""
if [[ "$MODE" == "build-and-simulate" ]]; then
  echo "[5/5] Run the exact eleven-case simulation-only TxV1 suite"
  [[ -x "$AGAVE_BIN_DIR/solana" && -x "$AGAVE_BIN_DIR/solana-test-validator" ]] \
    || fail "Agave bin directory is incomplete"
  [[ -f "$CASE_BUNDLE_DIR/bundle.json" ]] || fail "eleven-case bundle is missing bundle.json"
  bundle_pool=$(jq -er '.poolSbf' "$CASE_BUNDLE_DIR/bundle.json")
  bundle_verifier=$(jq -er '.verifierSbf' "$CASE_BUNDLE_DIR/bundle.json")
  [[ "$(sha_file "$CASE_BUNDLE_DIR/$bundle_pool")" == "$(sha_file "$OUTPUT_DIR/sbf/aspis_pool.so")" ]] \
    || fail "case bundle Pool SBF differs from the reproducible candidate"
  [[ "$(sha_file "$CASE_BUNDLE_DIR/$bundle_verifier")" == "$(sha_file "$OUTPUT_DIR/sbf/aspis_verifier.so")" ]] \
    || fail "case bundle verifier SBF differs from the reproducible candidate"
  bash "$WORK_DIR/source-a/scripts/v7_txv1_disposable_agave_simulate.sh" \
    "$AGAVE_BIN_DIR" "$CASE_BUNDLE_DIR" "$OUTPUT_DIR/txv1-suite"
  suite_sha256=$(sha_file "$OUTPUT_DIR/txv1-suite/suite.json")
  suite_status="PASS"
else
  echo "[5/5] Eleven-case Agave suite not requested; release gate remains open"
fi

jq -n \
  --arg sbfRecordSha256 "$(sha_file "$OUTPUT_DIR/reproducible-sbf.json")" \
  --arg suiteStatus "$suite_status" \
  --arg suiteSha256 "$suite_sha256" '
  {
    schema: "aspis.v7.one-tx-release-replay-summary.v1",
    reproducibleSbf: "PASS",
    reproducibleSbfRecordSha256: $sbfRecordSha256,
    disposableAgaveElevenCaseSuite: $suiteStatus,
    disposableAgaveSuiteSha256: (if $suiteSha256 == "" then null else $suiteSha256 end),
    publicDevnetLifecycle: "NOT_EXECUTED",
    signed: false,
    submitted: false,
    deployed: false,
    localBuildAndSimulationEvidenceComplete: ($suiteStatus == "PASS"),
    releaseReady: false
  }' >"$OUTPUT_DIR/summary.json"

echo "PASS: reproducible SBF build completed"
if [[ "$suite_status" == "PASS" ]]; then
  echo "PASS: eleven-case disposable Agave TxV1 simulation suite completed"
else
  echo "OPEN GATE: eleven-case disposable Agave TxV1 simulation suite was not executed"
fi
echo "No transaction was signed, submitted, or deployed."
(
  cd "$OUTPUT_DIR"
  find . -type f ! -name SHA256SUMS -print0 \
    | sort -z \
    | xargs -0 sha256sum >SHA256SUMS
)
