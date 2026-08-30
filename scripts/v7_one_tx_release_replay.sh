#!/usr/bin/env bash
set -euo pipefail

readonly ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly PREFLIGHT="$ROOT/release/v7-one-tx-candidate-preflight-v1"
readonly MANIFEST="$PREFLIGHT/manifest.json"
readonly VERIFY_INPUTS="$PREFLIGHT/verify-inputs.sh"
readonly TEMPLATE_BUNDLE="$ROOT/results/v7-one-tx-agave-bundle-template-20260830"
readonly BUNDLE_VERIFY="$ROOT/scripts/v7_txv1_bundle_verify.sh"
readonly AGAVE_RUNNER="$ROOT/scripts/v7_txv1_disposable_agave_simulate.sh"

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
    <new-output-dir> <agave-4.2+-bin-dir>

The build modes require Linux x86_64, a cgroup-v2 scope capped at
MemoryHigh<=9 GiB, MemoryMax<=12 GiB and MemorySwapMax=0, and:

  ASPIS_V7_TOOLCHAIN_CAPTURE_ROOT=<directory containing both
    platform-tools-v1.48/, solana-active-release/, and host-rust-stable/
    from the frozen platform-specific Linux x86_64 toolchain inventories>
  ASPIS_V7_CARGO_HOME=<exact offline Cargo cache matching the frozen
    428-package and 394-index-entry content inventory>

Both build modes produce two independent SBF builds and materialize the frozen
eleven-case fixture with the resulting Pool/verifier bytes. The simulation mode
also requires Agave 4.2+ and runs only simulateTransaction against disposable
validators. No mode signs, submits, deploys, or mutates a public cluster.
USAGE
  exit 2
}

[[ -f "$MANIFEST" && -x "$VERIFY_INPUTS" && -x "$BUNDLE_VERIFY" && -x "$AGAVE_RUNNER" ]] \
  || fail "V7 preflight or replay harness is incomplete"

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
    [[ $# -eq 3 ]] || usage
    ;;
  *) usage ;;
esac

readonly OUTPUT_DIR=$2
readonly AGAVE_BIN_DIR=${3:-}

for command_name in awk cmp cp find git jq sed sort stat tar uname wc xargs; do
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
readonly HOST_RUST_ROOT="$TOOLCHAIN_CAPTURE_ROOT/host-rust-stable"
readonly CARGO_BUILD_SBF="$SOLANA_ACTIVE_ROOT/bin/cargo-build-sbf"
readonly SBF_SDK="$SOLANA_ACTIVE_ROOT/bin/platform-tools-sdk/sbf"
readonly HOST_CARGO="$HOST_RUST_ROOT/bin/cargo"
readonly HOST_RUSTC="$HOST_RUST_ROOT/bin/rustc"
readonly BUILD_PATH="$HOST_RUST_ROOT/bin:$SOLANA_ACTIVE_ROOT/bin:/usr/bin:/bin"
readonly CARGO_HOME_ROOT=${ASPIS_V7_CARGO_HOME:-}
readonly CARGO_CACHE_PROVENANCE="$ROOT/$(jq -er '.toolchain.offlineCargoCache.provenancePath' "$MANIFEST")"
readonly CARGO_CACHE_PACKAGES="$ROOT/$(jq -er '.toolchain.offlineCargoCache.packagesPath' "$MANIFEST")"
readonly CARGO_CACHE_INDEX="$ROOT/$(jq -er '.toolchain.offlineCargoCache.indexPath' "$MANIFEST")"
[[ -x "$CARGO_BUILD_SBF" ]] || fail "frozen cargo-build-sbf is missing"
[[ -x "$HOST_CARGO" && -x "$HOST_RUSTC" ]] || fail "frozen host Cargo/Rust pair is missing"
[[ -x "$PLATFORM_TOOLS_ROOT/rust/bin/rustc" ]] || fail "frozen platform rustc is missing"
[[ -x "$PLATFORM_TOOLS_ROOT/llvm/bin/clang-19" ]] || fail "frozen platform clang is missing"
[[ -d "$SBF_SDK" ]] || fail "frozen SBF SDK is missing"
[[ -n "$CARGO_HOME_ROOT" && -d "$CARGO_HOME_ROOT/registry" ]] \
  || fail "ASPIS_V7_CARGO_HOME must name the frozen offline Cargo cache"

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
(( MEMORY_HIGH <= REQUIRED_HIGH )) || fail "MemoryHigh exceeds the frozen limit: $REQUIRED_HIGH bytes"
(( MEMORY_MAX <= REQUIRED_MAX )) || fail "MemoryMax exceeds the frozen limit: $REQUIRED_MAX bytes"
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

verify_offline_cargo_cache() {
  local snapshot=$1
  local name version source archive_path archive_bytes archive_sha
  local source_path source_files source_identity source_bytes source_sha
  local archive source_dir source_inventory actual_archive_bytes actual_archive_sha
  local actual_source_files actual_source_bytes actual_source_sha
  local index_path index_bytes index_sha index_file
  : >"$snapshot"
  while IFS=$'\t' read -r name version source archive_path archive_bytes archive_sha \
      source_path source_files source_identity; do
    archive="$CARGO_HOME_ROOT/$archive_path"
    source_dir="$CARGO_HOME_ROOT/$source_path"
    [[ -f "$archive" && -d "$source_dir" ]] \
      || fail "frozen offline Cargo package is missing: $name $version"
    actual_archive_bytes=$(stat -c %s "$archive")
    actual_archive_sha=$(sha_file "$archive")
    [[ "$actual_archive_bytes" == "$archive_bytes" && "$actual_archive_sha" == "$archive_sha" ]] \
      || fail "offline Cargo archive changed: $name $version"
    source_inventory="$WORK_DIR/cache-source-inventory"
    (
      cd "$source_dir"
      LC_ALL=C find . -type f -print0 | LC_ALL=C sort -z \
        | while IFS= read -r -d '' file; do
            printf '%s\t%s\t%s\n' "${file#./}" "$(stat -c %s "$file")" "$(sha_file "$file")"
          done
    ) >"$source_inventory"
    actual_source_files=$(wc -l <"$source_inventory" | tr -d ' ')
    actual_source_bytes=$(awk -F'\t' '{sum += $2} END {print sum + 0}' "$source_inventory")
    actual_source_sha=$(sha_file "$source_inventory")
    source_bytes=${source_identity%%:*}
    source_sha=${source_identity#*:}
    [[ "$actual_source_files" == "$source_files" && "$actual_source_bytes" == "$source_bytes" \
        && "$actual_source_sha" == "$source_sha" ]] \
      || fail "offline Cargo extracted source changed: $name $version"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
      "$name" "$version" "$source" "$archive_path" "$archive_bytes" "$archive_sha" \
      "$source_path" "$source_files" "$source_identity" >>"$snapshot"
  done <"$CARGO_CACHE_PACKAGES"
  cmp -s "$snapshot" "$CARGO_CACHE_PACKAGES" \
    || fail "offline Cargo package inventory did not reproduce byte for byte"
  while IFS=$'\t' read -r index_path index_bytes index_sha; do
    index_file="$CARGO_HOME_ROOT/$index_path"
    [[ -f "$index_file" && "$(stat -c %s "$index_file")" == "$index_bytes" \
        && "$(sha_file "$index_file")" == "$index_sha" ]] \
      || fail "offline Cargo sparse-index entry changed: $index_path"
  done <"$CARGO_CACHE_INDEX"
}

"$VERIFY_INPUTS" >"$OUTPUT_DIR/input-audit.json"

echo "[1/6] Verify every byte in the frozen SBF toolchain"
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

[[ "$(sha_file "$HOST_CARGO")" == "$(jq -er '.toolchain.offlineCargoCache.hostCargoSha256' "$MANIFEST")" ]] \
  || fail "host Cargo bytes differ from the frozen offline-cache toolchain"
[[ "$(sha_file "$HOST_RUSTC")" == "$(jq -er '.toolchain.offlineCargoCache.hostRustcSha256' "$MANIFEST")" ]] \
  || fail "host rustc bytes differ from the frozen offline-cache toolchain"
host_cargo_version=$($HOST_CARGO --version)
host_rustc_version=$($HOST_RUSTC --version)
[[ "$host_cargo_version" == "$(jq -er '.hostCargo.version' "$CARGO_CACHE_PROVENANCE")" ]] \
  || fail "host Cargo version differs from the frozen offline-cache toolchain"
[[ "$host_rustc_version" == "$(jq -er '.hostRustc.version' "$CARGO_CACHE_PROVENANCE")" ]] \
  || fail "host rustc version differs from the frozen offline-cache toolchain"
verify_offline_cargo_cache "$OUTPUT_DIR/cargo-cache-before.tsv"

expected_version=$(jq -er '.toolchain.cargoBuildSbfVersion' "$MANIFEST")
actual_version=$($CARGO_BUILD_SBF --version)
[[ "$actual_version" == "$expected_version" ]] \
  || fail "cargo-build-sbf version differs from the frozen toolchain"
platform_rustc_version=$($PLATFORM_TOOLS_ROOT/rust/bin/rustc --version)
[[ "$platform_rustc_version" == "$(jq -er '.toolchain.platformRustc' "$MANIFEST")" ]] \
  || fail "platform rustc version differs from the frozen toolchain"
printf '%s\n' "$actual_version" >"$OUTPUT_DIR/cargo-build-sbf-version.txt"
printf '%s\n' "$platform_rustc_version" >"$OUTPUT_DIR/platform-rustc-version.txt"
printf '%s\n' "$host_cargo_version" >"$OUTPUT_DIR/host-cargo-version.txt"
printf '%s\n' "$host_rustc_version" >"$OUTPUT_DIR/host-rustc-version.txt"
"$PLATFORM_TOOLS_ROOT/llvm/bin/clang-19" --version >"$OUTPUT_DIR/platform-clang-version.txt"

echo "[2/6] Export two isolated copies of the exact da77 source"
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

for program in aspis-pool aspis-verifier; do
  manifest_path=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .manifest' "$MANIFEST")
  (
    cd "$WORK_DIR/source-a"
    CARGO_HOME="$CARGO_HOME_ROOT" CARGO_NET_OFFLINE=true PATH="$BUILD_PATH" \
      "$HOST_CARGO" metadata --offline --locked --format-version 1 \
      --manifest-path "$manifest_path"
  ) >"$OUTPUT_DIR/metadata-$program.json"
done
jq -r '.packages[] | select(.source != null) | [.name,.version,.source] | @tsv' \
  "$OUTPUT_DIR/metadata-aspis-pool.json" "$OUTPUT_DIR/metadata-aspis-verifier.json" \
  | LC_ALL=C sort -u >"$OUTPUT_DIR/metadata-registry-packages.tsv"
cut -f1-3 "$CARGO_CACHE_PACKAGES" >"$WORK_DIR/expected-registry-packages.tsv"
cmp -s "$OUTPUT_DIR/metadata-registry-packages.tsv" "$WORK_DIR/expected-registry-packages.tsv" \
  || fail "locked Pool/verifier metadata differs from the frozen offline Cargo package set"

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
    export CARGO_HOME="$CARGO_HOME_ROOT"
    export CARGO_NET_OFFLINE=true
    export LANG=C
    export LC_ALL=C
    export NO_DNA=1
    export PATH="$BUILD_PATH"
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

echo "[3/6] Build Pool and verifier in both isolated source copies"
for label in a b; do
  build_program "$label" aspis-pool
  build_program "$label" aspis-verifier
done

verify_offline_cargo_cache "$OUTPUT_DIR/cargo-cache-after.tsv"
cmp -s "$OUTPUT_DIR/cargo-cache-before.tsv" "$OUTPUT_DIR/cargo-cache-after.tsv" \
  || fail "offline Cargo cache content changed during the dual build"

echo "[4/6] Require A/B equality and freeze exact derived SBF identities"
mkdir -p "$OUTPUT_DIR/sbf"
build_records='[]'
for program in aspis-pool aspis-verifier; do
  output_name=$(jq -er --arg program "$program" '.programs[] | select(.name == $program) | .output' "$MANIFEST")
  expected_sha=$(jq -r --arg program "$program" '.programs[] | select(.name == $program) | .expectedSha256 // empty' "$MANIFEST")
  expected_bytes=$(jq -r --arg program "$program" '.programs[] | select(.name == $program) | .expectedBytes // empty' "$MANIFEST")
  artifact_a="$WORK_DIR/sbf-a-$program/$output_name"
  artifact_b="$WORK_DIR/sbf-b-$program/$output_name"
  cmp -s "$artifact_a" "$artifact_b" || fail "$program A/B SBFs are not byte-identical"
  actual_sha=$(sha_file "$artifact_a")
  actual_bytes=$(wc -c <"$artifact_a" | tr -d ' ')
  if [[ -n "$expected_sha" || -n "$expected_bytes" ]]; then
    [[ "$actual_sha" == "$expected_sha" && "$actual_bytes" == "$expected_bytes" ]] \
      || fail "$program SBF does not match its frozen reference"
  elif [[ "$program" != "aspis-pool" ]]; then
    fail "only the atomic-marker Pool may use a first-derived SBF identity"
  fi
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

pool_sha=$(sha_file "$OUTPUT_DIR/sbf/aspis_pool.so")
pool_bytes=$(wc -c <"$OUTPUT_DIR/sbf/aspis_pool.so" | tr -d ' ')
verifier_sha=$(sha_file "$OUTPUT_DIR/sbf/aspis_verifier.so")
verifier_bytes=$(wc -c <"$OUTPUT_DIR/sbf/aspis_verifier.so" | tr -d ' ')

jq -n \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$(jq -er '.source.tree' "$MANIFEST")" \
  --argjson sourceDateEpoch "$SOURCE_DATE_EPOCH" \
  --arg sourceArchiveASha256 "$SOURCE_ARCHIVE_A_SHA" \
  --arg sourceArchiveBSha256 "$SOURCE_ARCHIVE_B_SHA" \
  --arg toolchainInventorySha256 "$(jq -er '.toolchain.frozenInventory.sha256' "$MANIFEST")" \
  --arg offlineCargoCacheProvenanceSha256 "$(jq -er '.toolchain.offlineCargoCache.provenanceSha256' "$MANIFEST")" \
  --arg offlineCargoPackagesSha256 "$(sha_file "$OUTPUT_DIR/cargo-cache-after.tsv")" \
  --arg hostCargoSha256 "$(sha_file "$HOST_CARGO")" \
  --arg hostCargoVersion "$host_cargo_version" \
  --arg cargoBuildSbfSha256 "$expected_cargo_build_sbf_sha" \
  --arg cargoBuildSbfVersion "$actual_version" \
  --arg uname "$(<"$OUTPUT_DIR/uname.txt")" \
  --arg osReleaseSha256 "$(sha_file "$OUTPUT_DIR/os-release.txt")" \
  --arg poolSha256 "$pool_sha" \
  --arg verifierSha256 "$verifier_sha" \
  --argjson builds "$build_records" \
  --argjson poolBytes "$pool_bytes" \
  --argjson verifierBytes "$verifier_bytes" \
  --arg cgroup "$CGROUP_RELATIVE" \
  --argjson memoryHigh "$MEMORY_HIGH" \
  --argjson memoryMax "$MEMORY_MAX" \
  --argjson memorySwapMax "$MEMORY_SWAP_MAX" '
  {
    schema: "aspis.v7.one-tx-reproducible-sbf.v2",
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
      offlineCargoCacheProvenanceSha256: $offlineCargoCacheProvenanceSha256,
      offlineCargoPackagesSha256: $offlineCargoPackagesSha256,
      offlineCargoCacheVerifiedBeforeAndAfter: true,
      hostCargoSha256: $hostCargoSha256,
      hostCargoVersion: $hostCargoVersion,
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
      pool: {
        bytes: $poolBytes,
        sha256: $poolSha256,
        buildsByteIdentical: true,
        identityClassification: "FIRST_FRESH_DA77_ATOMIC_MARKER_FREEZE"
      },
      verifier: {
        bytes: $verifierBytes,
        sha256: $verifierSha256,
        buildsByteIdentical: true,
        matchesFrozenReference: true
      }
    },
    signed: false,
    submitted: false,
    deployed: false
  }' >"$OUTPUT_DIR/reproducible-sbf.json"

echo "[5/6] Materialize and verify the frozen eleven-case bundle"
readonly MATERIALIZED_BUNDLE="$OUTPUT_DIR/materialized-eleven-case-bundle"
mkdir -p "$MATERIALIZED_BUNDLE"
cp -R "$TEMPLATE_BUNDLE"/. "$MATERIALIZED_BUNDLE"/
mkdir -p "$MATERIALIZED_BUNDLE/sbf"
cp "$OUTPUT_DIR/sbf/aspis_pool.so" "$MATERIALIZED_BUNDLE/sbf/aspis_pool.so"
cp "$OUTPUT_DIR/sbf/aspis_verifier.so" "$MATERIALIZED_BUNDLE/sbf/aspis_verifier.so"
jq \
  --arg poolSha "$pool_sha" \
  --argjson poolBytes "$pool_bytes" '
  .poolSbfSha256 = $poolSha |
  .poolSbfBytes = $poolBytes |
  .sbfBindingComplete = true |
  .executionReady = true
' "$MATERIALIZED_BUNDLE/bundle.json" >"$WORK_DIR/materialized-bundle.json"
cp "$WORK_DIR/materialized-bundle.json" "$MATERIALIZED_BUNDLE/bundle.json"
(
  cd "$MATERIALIZED_BUNDLE"
  find . -type f ! -path './sbf/*' ! -name TEMPLATE-SHA256SUMS -print \
    | sort \
    | while IFS= read -r relative; do
        printf '%s  %s\n' "$(sha_file "$relative")" "${relative#./}"
      done >"$WORK_DIR/materialized-inventory"
)
cp "$WORK_DIR/materialized-inventory" "$MATERIALIZED_BUNDLE/TEMPLATE-SHA256SUMS"
"$BUNDLE_VERIFY" "$MATERIALIZED_BUNDLE" --materialized \
  >"$OUTPUT_DIR/materialized-bundle-audit.json"

suite_status="UNAVAILABLE_NOT_REQUESTED"
suite_sha256=""
if [[ "$MODE" == "build-and-simulate" ]]; then
  echo "[6/6] Execute the exact eleven-case simulation-only TxV1 suite"
  [[ -x "$AGAVE_BIN_DIR/solana" && -x "$AGAVE_BIN_DIR/solana-test-validator" ]] \
    || fail "Agave bin directory is incomplete"
  ASPIS_TXV1_WALLET_SOURCE_ROOT="$WORK_DIR/source-a" \
    "$AGAVE_RUNNER" "$AGAVE_BIN_DIR" "$MATERIALIZED_BUNDLE" "$OUTPUT_DIR/txv1-suite"
  suite_sha256=$(sha_file "$OUTPUT_DIR/txv1-suite/suite.json")
  suite_status="PASS"
else
  echo "[6/6] Agave suite not requested; runtime/CU gate remains open"
fi

jq -n \
  --arg sbfRecordSha256 "$(sha_file "$OUTPUT_DIR/reproducible-sbf.json")" \
  --arg poolSha256 "$pool_sha" \
  --arg materializedBundleSha256 "$(sha_file "$MATERIALIZED_BUNDLE/bundle.json")" \
  --arg materializedBundleAuditSha256 "$(sha_file "$OUTPUT_DIR/materialized-bundle-audit.json")" \
  --arg suiteStatus "$suite_status" \
  --arg suiteSha256 "$suite_sha256" '
  {
    schema: "aspis.v7.one-tx-release-replay-summary.v2",
    reproducibleSbf: "PASS",
    reproducibleSbfRecordSha256: $sbfRecordSha256,
    atomicMarkerPoolSbfSha256: $poolSha256,
    deterministicBundleMaterialized: true,
    materializedBundleSha256: $materializedBundleSha256,
    materializedBundleAuditSha256: $materializedBundleAuditSha256,
    disposableAgaveElevenCaseSuite: $suiteStatus,
    disposableAgaveSuiteSha256: (if $suiteSha256 == "" then null else $suiteSha256 end),
    publicDevnetLifecycle: "NOT_EXECUTED",
    signed: false,
    submitted: false,
    deployed: false,
    localBuildAndSimulationEvidenceComplete: ($suiteStatus == "PASS"),
    releaseReady: false
  }' >"$OUTPUT_DIR/summary.json"

echo "PASS: two byte-identical Pool and verifier SBF builds completed"
echo "PASS: deterministic eleven-case bundle materialized against those exact bytes"
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
