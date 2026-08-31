#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 5 ]]; then
  echo "usage: $0 <repo-root> <agave-bin-dir> <bundle-dir> <new-output-dir> <task-cargo-home>" >&2
  exit 2
fi

readonly REPO_ROOT=$1
readonly AGAVE_BIN_DIR=$2
readonly BUNDLE_DIR=$3
readonly OUTPUT_DIR=$4
readonly TASK_CARGO_HOME=$5

[[ -d "$REPO_ROOT/.git" || -f "$REPO_ROOT/.git" ]] || {
  echo "isolated repository is unavailable: $REPO_ROOT" >&2
  exit 2
}
[[ -x "$REPO_ROOT/scripts/v7_txv1_disposable_agave_simulate.sh" ]] || {
  echo "simulation-only runner is unavailable" >&2
  exit 2
}
[[ -d "$TASK_CARGO_HOME/registry" ]] || {
  echo "task-owned offline Cargo registry is unavailable" >&2
  exit 2
}
[[ ! -e "$OUTPUT_DIR" ]] || {
  echo "refusing to overwrite output: $OUTPUT_DIR" >&2
  exit 2
}

mkdir -p "$OUTPUT_DIR"
export CARGO_HOME="$TASK_CARGO_HOME"
if [[ -n "${ASPIS_REGISTRY_V2_CARGO_TARGET_DIR:-}" ]]; then
  [[ "$ASPIS_REGISTRY_V2_CARGO_TARGET_DIR" == /* \
      && -d "$ASPIS_REGISTRY_V2_CARGO_TARGET_DIR" ]] || {
    echo "explicit Cargo target reuse must name an existing absolute directory" >&2
    exit 2
  }
  export CARGO_TARGET_DIR="$ASPIS_REGISTRY_V2_CARGO_TARGET_DIR"
else
  export CARGO_TARGET_DIR="$OUTPUT_DIR/cargo-target"
fi
export CARGO_BUILD_JOBS=1
export CARGO_NET_OFFLINE=true
export NO_DNA=1
export RUSTUP_HOME=/home/dombarker/.rustup
export PATH="/home/dombarker/.cargo/bin:$AGAVE_BIN_DIR:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"
printf '%s\n' "$CARGO_TARGET_DIR" >"$OUTPUT_DIR/cargo-target-source.txt"

cd "$REPO_ROOT"
/usr/bin/time -v -o "$OUTPUT_DIR/resource.time" \
  scripts/v7_txv1_disposable_agave_simulate.sh \
  "$AGAVE_BIN_DIR" "$BUNDLE_DIR" "$OUTPUT_DIR/evidence" \
  >"$OUTPUT_DIR/runner.stdout" 2>"$OUTPUT_DIR/runner.stderr"

sha256sum \
  "$BUNDLE_DIR/bundle.json" \
  "$BUNDLE_DIR/TEMPLATE-SHA256SUMS" \
  "$OUTPUT_DIR/evidence/suite.json" \
  >"$OUTPUT_DIR/replay-bindings.sha256"
