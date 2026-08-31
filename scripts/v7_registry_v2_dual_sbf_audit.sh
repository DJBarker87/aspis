#!/usr/bin/env bash
set -euo pipefail

readonly ROOT=$(cd "$(dirname "$0")/.." && pwd)
readonly MANIFEST="$ROOT/release/v7-registry-v2-runtime-audit-v1/manifest.json"
readonly VERIFY_INPUTS="$ROOT/release/v7-registry-v2-runtime-audit-v1/verify-inputs.sh"

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
usage: scripts/v7_registry_v2_dual_sbf_audit.sh <new-output-directory>

Required environment:

  ASPIS_V7_CARGO_BUILD_SBF  exact solana-cargo-build-sbf 2.3.0 wrapper
  ASPIS_V7_SBF_SDK          exact v1.48 SBF SDK directory
  ASPIS_V7_LLVM_OBJDUMP     exact v1.48 llvm-objdump
  ASPIS_V7_PLATFORM_RUSTC   exact v1.48 platform rustc
  ASPIS_V7_CLANG19          exact v1.48 clang-19
  ASPIS_V7_CARGO_HOME       provenance-frozen complete offline Cargo cache
  ASPIS_V7_RUSTUP_HOME      pinned host rustup home with the solana toolchain
  ASPIS_V7_HOST_RUST_BIN    optional pinned host cargo/rustup proxy directory

Run only on Linux x86_64 inside a cgroup-v2 scope with MemoryHigh no larger
than 10 GiB, MemoryMax no larger than 12 GiB, and MemorySwapMax=0. The script
builds Pool, verifier and Registry serially from two isolated source exports,
requires byte equality and the frozen artifact identities, rejects every SBF
stack-overflow diagnostic, and derives per-function offsets from each
unstripped Pool binary. It never deploys, signs or submits a transaction.
USAGE
  exit 2
}

[[ $# -eq 1 ]] || usage
readonly OUTPUT_DIR=$1
[[ "$OUTPUT_DIR" == /* && "$OUTPUT_DIR" != "/" ]] \
  || fail "output directory must be an explicit absolute non-root path"
[[ ! -e "$OUTPUT_DIR" ]] || fail "refusing to overwrite output directory: $OUTPUT_DIR"

for command_name in awk cmp cp find git grep jq mkdir perl sed sort stat tar tr uname wc; do
  require_command "$command_name"
done
[[ -x /usr/bin/time ]] || fail "/usr/bin/time is required"
[[ -f "$MANIFEST" && -x "$VERIFY_INPUTS" ]] || fail "release audit inputs are incomplete"
[[ "$(uname -s)" == "Linux" && "$(uname -m)" == "x86_64" ]] \
  || fail "dual SBF audit requires Linux x86_64"

readonly CARGO_BUILD_SBF=${ASPIS_V7_CARGO_BUILD_SBF:-}
readonly SBF_SDK=${ASPIS_V7_SBF_SDK:-}
readonly LLVM_OBJDUMP=${ASPIS_V7_LLVM_OBJDUMP:-}
readonly PLATFORM_RUSTC=${ASPIS_V7_PLATFORM_RUSTC:-}
readonly CLANG19=${ASPIS_V7_CLANG19:-}
readonly CARGO_HOME_ROOT=${ASPIS_V7_CARGO_HOME:-}
readonly RUSTUP_HOME_ROOT=${ASPIS_V7_RUSTUP_HOME:-}
readonly HOST_RUST_BIN=${ASPIS_V7_HOST_RUST_BIN:-}
readonly ORIGINAL_PATH=$PATH

for executable in "$CARGO_BUILD_SBF" "$LLVM_OBJDUMP" "$PLATFORM_RUSTC" "$CLANG19"; do
  [[ -n "$executable" && -x "$executable" ]] || fail "missing required pinned executable: $executable"
done
[[ -n "$SBF_SDK" && -d "$SBF_SDK" ]] || fail "ASPIS_V7_SBF_SDK is missing"
[[ -n "$CARGO_HOME_ROOT" && -d "$CARGO_HOME_ROOT/registry" ]] \
  || fail "ASPIS_V7_CARGO_HOME is not a complete offline Cargo home"
[[ -n "$RUSTUP_HOME_ROOT" && -d "$RUSTUP_HOME_ROOT/toolchains" ]] \
  || fail "ASPIS_V7_RUSTUP_HOME is not a rustup home"
if [[ -n "$HOST_RUST_BIN" && ! -d "$HOST_RUST_BIN" ]]; then
  fail "ASPIS_V7_HOST_RUST_BIN is not a directory"
fi

[[ "$(sha_file "$CARGO_BUILD_SBF")" == "$(jq -er '.toolchain.cargoBuildSbfSha256' "$MANIFEST")" ]] \
  || fail "cargo-build-sbf bytes differ from the frozen wrapper"
[[ "$(sha_file "$LLVM_OBJDUMP")" == "$(jq -er '.toolchain.llvmObjdumpSha256' "$MANIFEST")" ]] \
  || fail "llvm-objdump bytes differ from the frozen v1.48 tool"
[[ "$(sha_file "$PLATFORM_RUSTC")" == "$(jq -er '.toolchain.platformRustcSha256' "$MANIFEST")" ]] \
  || fail "platform rustc bytes differ from the frozen v1.48 tool"
[[ "$(sha_file "$CLANG19")" == "$(jq -er '.toolchain.clang19Sha256' "$MANIFEST")" ]] \
  || fail "clang-19 bytes differ from the frozen v1.48 tool"
[[ "$($CARGO_BUILD_SBF --version)" == "$(jq -er '.toolchain.cargoBuildSbfVersion' "$MANIFEST")" ]] \
  || fail "cargo-build-sbf version differs from the frozen release toolchain"
[[ "$($PLATFORM_RUSTC --version)" == "$(jq -er '.toolchain.platformRustc' "$MANIFEST")" ]] \
  || fail "platform rustc version differs from the frozen release toolchain"

readonly CGROUP_RELATIVE=$(awk -F: '$1 == "0" {print $3; exit}' /proc/self/cgroup)
readonly CGROUP_DIR="/sys/fs/cgroup$CGROUP_RELATIVE"
for control in memory.high memory.max memory.peak memory.swap.max memory.swap.current memory.swap.peak; do
  [[ -r "$CGROUP_DIR/$control" ]] || fail "cgroup-v2 control is unavailable: $control"
done
readonly MEMORY_HIGH=$(<"$CGROUP_DIR/memory.high")
readonly MEMORY_MAX=$(<"$CGROUP_DIR/memory.max")
readonly MEMORY_SWAP_MAX=$(<"$CGROUP_DIR/memory.swap.max")
[[ "$MEMORY_HIGH" =~ ^[0-9]+$ && "$MEMORY_MAX" =~ ^[0-9]+$ && "$MEMORY_SWAP_MAX" =~ ^[0-9]+$ ]] \
  || fail "finite numeric cgroup limits are required"
(( MEMORY_HIGH <= $(jq -er '.toolchain.requiredCgroup.memoryHighBytesAtMost' "$MANIFEST") )) \
  || fail "MemoryHigh exceeds 10 GiB"
(( MEMORY_MAX <= $(jq -er '.toolchain.requiredCgroup.memoryMaxBytesAtMost' "$MANIFEST") )) \
  || fail "MemoryMax exceeds 12 GiB"
(( MEMORY_SWAP_MAX == 0 )) || fail "MemorySwapMax must be zero"

mkdir -p "$OUTPUT_DIR"
"$VERIFY_INPUTS" >"$OUTPUT_DIR/input-audit.json"
uname -a >"$OUTPUT_DIR/uname.txt"
cp /etc/os-release "$OUTPUT_DIR/os-release.txt"
printf '%s\n' "$($CARGO_BUILD_SBF --version)" >"$OUTPUT_DIR/cargo-build-sbf-version.txt"
printf '%s\n' "$($PLATFORM_RUSTC --version)" >"$OUTPUT_DIR/platform-rustc-version.txt"
"$CLANG19" --version >"$OUTPUT_DIR/clang-version.txt"
"$LLVM_OBJDUMP" --version >"$OUTPUT_DIR/llvm-objdump-version.txt"

readonly SOURCE_COMMIT=$(jq -er '.releaseEvidence.commit' "$MANIFEST")
readonly SOURCE_PARENT=$(jq -er '.releaseEvidence.productionSourceParent' "$MANIFEST")
readonly SOURCE_DATE_EPOCH=$(git -C "$ROOT" show -s --format=%ct "$SOURCE_PARENT")
readonly SOURCE_PATHS=(
  .cargo
  Cargo.toml
  Cargo.lock
  crates
  programs
  audit/poseidon-pair-probe/program
  xtask
)

for label in a b; do
  mkdir -p "$OUTPUT_DIR/source-$label"
  git -C "$ROOT" archive "$SOURCE_COMMIT" "${SOURCE_PATHS[@]}" >"$OUTPUT_DIR/source-$label.tar"
  tar -xf "$OUTPUT_DIR/source-$label.tar" -C "$OUTPUT_DIR/source-$label"
  [[ "$(sha_file "$OUTPUT_DIR/source-$label/Cargo.lock")" == \
      "$(jq -er '.source.cargoLockSha256' "$MANIFEST")" ]] \
    || fail "source-$label Cargo.lock differs from the frozen source"
done
[[ "$(sha_file "$OUTPUT_DIR/source-a.tar")" == "$(sha_file "$OUTPUT_DIR/source-b.tar")" ]] \
  || fail "independent source archives differ"

readonly BUILD_PATH=$(dirname "$CARGO_BUILD_SBF"):${HOST_RUST_BIN:+$HOST_RUST_BIN:}$(dirname "$PLATFORM_RUSTC"):$ORIGINAL_PATH

build_program() {
  local label=$1
  local program=$2
  local source_dir="$OUTPUT_DIR/source-$label"
  local target_dir="$OUTPUT_DIR/target-$label"
  local sbf_dir="$OUTPUT_DIR/sbf-$label-$program"
  local manifest_path features output
  manifest_path=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .manifest' "$MANIFEST")
  features=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .features' "$MANIFEST")
  output=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .output' "$MANIFEST")
  mkdir -p "$target_dir" "$sbf_dir"
  local -a feature_args=()
  if [[ -n "$features" ]]; then
    feature_args=(--features "$features")
  fi
  (
    cd "$source_dir"
    export CARGO_BUILD_JOBS=1
    export CARGO_HOME="$CARGO_HOME_ROOT"
    export CARGO_NET_OFFLINE=true
    export CARGO_TARGET_DIR="$target_dir"
    export LANG=C
    export LC_ALL=C
    export NO_DNA=1
    export PATH="$BUILD_PATH"
    export RUSTUP_HOME="$RUSTUP_HOME_ROOT"
    export SOURCE_DATE_EPOCH
    export TZ=UTC
    unset CARGO_ENCODED_RUSTFLAGS RUSTFLAGS
    /usr/bin/time -v -o "$OUTPUT_DIR/build-$label-$program.time" \
      "$CARGO_BUILD_SBF" \
      --manifest-path "$manifest_path" \
      --no-default-features \
      "${feature_args[@]}" \
      --arch v0 \
      --offline \
      --skip-tools-install \
      --tools-version v1.48 \
      --sbf-sdk "$SBF_SDK" \
      --sbf-out-dir "$sbf_dir" \
      -- \
      --locked
  ) >"$OUTPUT_DIR/build-$label-$program.log" 2>&1
  [[ -f "$sbf_dir/$output" ]] || fail "build $label omitted $output"
}

for label in a b; do
  for program in aspis-pool aspis-verifier aspis-registry; do
    build_program "$label" "$program"
  done
done

readonly OVERFLOW_PATTERN='Stack offset of|Estimated function frame size|exceeded max offset|undefined behavior during execution'
for log in "$OUTPUT_DIR"/build-*.log; do
  if grep -Eq "$OVERFLOW_PATTERN" "$log"; then
    fail "SBF stack analyzer reported an overflow: $log"
  fi
done

analyze_unstripped() {
  local label=$1
  local program=$2
  local output unstripped report
  output=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .output' "$MANIFEST")
  unstripped="$OUTPUT_DIR/target-$label/sbpf-solana-solana/release/$output"
  report="$OUTPUT_DIR/stack-$label-$program.tsv"
  [[ -f "$unstripped" ]] || fail "missing unstripped SBF for stack audit: $unstripped"
  "$LLVM_OBJDUMP" --disassemble --demangle "$unstripped" | perl -ne '
    if (/^[0-9a-f]+ <(.+)>:/) { $function = $1 }
    while (/r10 - 0x([0-9a-f]+)/g) {
      $offset = hex($1);
      $maximum{$function} = $offset if $offset > ($maximum{$function} // 0);
    }
    END {
      for $function (sort keys %maximum) {
        print "$maximum{$function}\t$function\n";
      }
    }
  ' >"$report"
  [[ -s "$report" ]] || fail "stack disassembly produced no frame accesses: $program $label"
  local maximum
  maximum=$(awk -F'\t' 'BEGIN {m=0} $1+0 > m {m=$1+0} END {print m}' "$report")
  (( maximum <= 4096 )) || fail "$program $label contains a stack access beyond 4096 bytes"
}

for label in a b; do
  for program in aspis-pool aspis-verifier aspis-registry; do
    analyze_unstripped "$label" "$program"
  done
  planner=$(awk -F'\t' '
    $2 ~ /aspis_pool::pair_forest::plan_pair_forest_checkpoint_accounts_v1::/ && $1+0 > m {m=$1+0; found=1}
    END {if (found) print m}
  ' "$OUTPUT_DIR/stack-$label-aspis-pool.tsv")
  decoder=$(awk -F'\t' '
    $2 ~ /aspis_pool::pair_forest::decode_checkpoint_lanes_box_v1::/ && $1+0 > m {m=$1+0; found=1}
    END {if (found) print m}
  ' "$OUTPUT_DIR/stack-$label-aspis-pool.tsv")
  [[ "$planner" == "2912" ]] || fail "Pool planner stack offset differs in build $label: $planner"
  [[ "$decoder" == "3024" ]] || fail "Pool lane decoder stack offset differs in build $label: $decoder"
done

mkdir -p "$OUTPUT_DIR/frozen-sbf"
program_records='[]'
build_records='[]'
for program in aspis-pool aspis-verifier aspis-registry; do
  output=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .output' "$MANIFEST")
  expected_sha=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .expectedSha256' "$MANIFEST")
  expected_bytes=$(jq -er --arg name "$program" '.programs[] | select(.name == $name) | .expectedBytes' "$MANIFEST")
  artifact_a="$OUTPUT_DIR/sbf-a-$program/$output"
  artifact_b="$OUTPUT_DIR/sbf-b-$program/$output"
  cmp -s "$artifact_a" "$artifact_b" || fail "$program A/B artifacts are not byte-identical"
  actual_sha=$(sha_file "$artifact_a")
  actual_bytes=$(wc -c <"$artifact_a" | tr -d ' ')
  [[ "$actual_sha" == "$expected_sha" && "$actual_bytes" == "$expected_bytes" ]] \
    || fail "$program does not reproduce its frozen Registry V2 artifact"
  cp "$artifact_a" "$OUTPUT_DIR/frozen-sbf/$output"
  maximum_stack=$(awk -F'\t' 'BEGIN {m=0} $1+0 > m {m=$1+0} END {print m}' \
    "$OUTPUT_DIR/stack-a-$program.tsv")
  program_records=$(jq -cn \
    --argjson prior "$program_records" \
    --arg name "$program" \
    --arg output "$output" \
    --arg sha256 "$actual_sha" \
    --argjson bytes "$actual_bytes" \
    --argjson maximumStackAccessBytes "$maximum_stack" '
      $prior + [{
        name: $name,
        output: $output,
        bytes: $bytes,
        sha256: $sha256,
        buildsByteIdentical: true,
        matchesFrozenRegistryV2Artifact: true,
        maximumObservedStackAccessBytes: $maximumStackAccessBytes,
        stackLimitBytes: 4096,
        stackGatePassed: ($maximumStackAccessBytes <= 4096)
      }]
  ')
  for label in a b; do
    time_file="$OUTPUT_DIR/build-$label-$program.time"
    log_file="$OUTPUT_DIR/build-$label-$program.log"
    rss=$(awk -F: '/Maximum resident set size \(kbytes\)/ {gsub(/[[:space:]]/, "", $2); print $2}' "$time_file")
    elapsed=$(sed -n 's/^[[:space:]]*Elapsed (wall clock) time (h:mm:ss or m:ss):[[:space:]]*//p' "$time_file")
    swaps=$(awk -F: '/Swaps/ {gsub(/[[:space:]]/, "", $2); print $2}' "$time_file")
    exit_status=$(awk -F: '/Exit status/ {gsub(/[[:space:]]/, "", $2); print $2}' "$time_file")
    [[ "$rss" =~ ^[0-9]+$ && "$swaps" == "0" && "$exit_status" == "0" && -n "$elapsed" ]] \
      || fail "invalid resource evidence for $program build $label"
    build_records=$(jq -cn \
      --argjson prior "$build_records" \
      --arg copy "$label" \
      --arg program "$program" \
      --arg elapsed "$elapsed" \
      --argjson maximumResidentSetKiB "$rss" \
      --arg logSha256 "$(sha_file "$log_file")" \
      --arg timeSha256 "$(sha_file "$time_file")" '
        $prior + [{
          copy: $copy,
          program: $program,
          elapsed: $elapsed,
          maximumResidentSetKiB: $maximumResidentSetKiB,
          swaps: 0,
          exitStatus: 0,
          logSha256: $logSha256,
          timeSha256: $timeSha256
        }]
    ')
  done
done

readonly MEMORY_PEAK=$(<"$CGROUP_DIR/memory.peak")
readonly MEMORY_SWAP_CURRENT=$(<"$CGROUP_DIR/memory.swap.current")
readonly MEMORY_SWAP_PEAK=$(<"$CGROUP_DIR/memory.swap.peak")
[[ "$MEMORY_SWAP_CURRENT" == "0" && "$MEMORY_SWAP_PEAK" == "0" ]] \
  || fail "cgroup used swap during the dual build"

jq -n \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$(jq -er '.releaseEvidence.tree' "$MANIFEST")" \
  --arg sourceArchiveSha256 "$(sha_file "$OUTPUT_DIR/source-a.tar")" \
  --arg cargoBuildSbfSha256 "$(sha_file "$CARGO_BUILD_SBF")" \
  --arg llvmObjdumpSha256 "$(sha_file "$LLVM_OBJDUMP")" \
  --arg cgroup "$CGROUP_RELATIVE" \
  --argjson memoryHighBytes "$MEMORY_HIGH" \
  --argjson memoryMaxBytes "$MEMORY_MAX" \
  --argjson memoryPeakBytes "$MEMORY_PEAK" \
  --argjson builds "$build_records" \
  --argjson programs "$program_records" '
  {
    schema: "aspis.v7.registry-v2-reproducible-sbf-stack-audit.v1",
    source: {
      commit: $sourceCommit,
      tree: $sourceTree,
      independentCopies: 2,
      sourceArchiveSha256: $sourceArchiveSha256,
      sourceArchivesByteIdentical: true
    },
    toolchain: {
      cargoBuildSbfSha256: $cargoBuildSbfSha256,
      llvmObjdumpSha256: $llvmObjdumpSha256,
      platformTools: "v1.48",
      architecture: "v0",
      offline: true,
      locked: true
    },
    cgroup: {
      path: $cgroup,
      memoryHighBytes: $memoryHighBytes,
      memoryMaxBytes: $memoryMaxBytes,
      memoryPeakBytes: $memoryPeakBytes,
      memorySwapMaxBytes: 0,
      memorySwapCurrentBytes: 0,
      memorySwapPeakBytes: 0
    },
    builds: $builds,
    programs: $programs,
    allBuildsByteIdentical: true,
    allArtifactsMatchFrozenRegistryV2Evidence: true,
    allStackGatesPassed: true,
    signed: false,
    submitted: false,
    deployed: false
  }
' >"$OUTPUT_DIR/reproducible-sbf-stack-audit.json"

echo "Registry V2 dual SBF/stack audit PASS: $OUTPUT_DIR/reproducible-sbf-stack-audit.json"
