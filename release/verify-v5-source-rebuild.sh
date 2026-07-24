#!/usr/bin/env bash
#
# Rebuild the frozen V5 Tag-67 SBF from its documented clean source commit.
#
# This is deliberately separate from the bundle's offline verify.sh. The
# offline verifier needs only jq and SHA-256. This source-rebuild verifier also
# requires the exact Solana SBF toolchain and fails if any required tool,
# source identity, formal-entrypoint identity, build step, or byte comparison
# is unavailable.

set -euo pipefail

readonly FROZEN_SOURCE_COMMIT="06788d44d30ea8cbd391899dddaf6f0acc6e4a3f"
readonly FROZEN_SOURCE_TREE="9b6bdfddb3c213addc2bb705c8130cce4fb2c351"
readonly FROZEN_SBF_SHA256="4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40"
readonly FROZEN_SBF_BYTES="1258496"
readonly FROZEN_CARGO_TOML_SHA256="9c9a3948723bfcab692c012a26df34d88352e359f90affd0759097287cb2c832"
readonly FROZEN_CARGO_LOCK_SHA256="5b407dc5cb239633b6d3cad6a05ac38570887f2393c74b5e2f03634793bfb176"

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "required command is unavailable: $1"
}

for command_name in cargo cmp git jq tar; do
  require_command "$command_name"
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

readonly ROOT="$(git rev-parse --show-toplevel)"
readonly BUNDLE="$ROOT/release/aspis-v5-tag67-frozen-candidate-v1"
readonly MANIFEST="$BUNDLE/manifest.json"
readonly PARITY="$BUNDLE/provenance/source-parity-attestation.json"
readonly CARGO_BUILD_SBF="${V5_CARGO_BUILD_SBF:?set V5_CARGO_BUILD_SBF to the pinned cargo-build-sbf executable}"
readonly SBF_SDK="${V5_SBF_SDK:?set V5_SBF_SDK to the pinned platform-tools SDK directory}"
readonly PLATFORM_TOOLS="${V5_PLATFORM_TOOLS_ROOT:?set V5_PLATFORM_TOOLS_ROOT to the extracted v1.48 platform-tools directory}"
readonly OUT="${V5_PROVENANCE_OUT:?set V5_PROVENANCE_OUT to an empty output directory}"

[[ -f "$MANIFEST" ]] || fail "V5 manifest is missing"
[[ -f "$PARITY" ]] || fail "V5 source-parity attestation is missing"
[[ -f "$BUNDLE/verify.sh" ]] || fail "V5 offline verifier is missing"
[[ -x "$CARGO_BUILD_SBF" ]] || fail "cargo-build-sbf is not an executable: $CARGO_BUILD_SBF"
[[ -d "$SBF_SDK" ]] || fail "SBF SDK directory is missing: $SBF_SDK"
[[ -x "$PLATFORM_TOOLS/rust/bin/rustc" ]] || fail "platform-tools rustc is missing"
[[ -x "$PLATFORM_TOOLS/llvm/bin/clang" ]] || fail "platform-tools clang is missing"
[[ -f "$PLATFORM_TOOLS/version.md" ]] || fail "platform-tools version.md is missing"

mkdir -p "$OUT"
[[ -z "$(find "$OUT" -mindepth 1 -maxdepth 1 -print -quit)" ]] \
  || fail "V5 provenance output directory must be empty: $OUT"

tmp="$(mktemp -d "${TMPDIR:-/tmp}/aspis-v5-source-rebuild.XXXXXX")"
cleanup() {
  status=$?
  trap - EXIT
  rm -rf -- "$tmp"
  exit "$status"
}
trap cleanup EXIT
trap 'exit 1' HUP INT TERM

echo "[1/6] Verify the immutable V5 release bundle"
bash "$BUNDLE/verify.sh" | tee "$OUT/bundle-verification.log"

echo "[2/6] Bind the documented source commit and frozen artifact"
manifest_commit="$(jq -er '.source.commit' "$MANIFEST")"
manifest_tree="$(jq -er '.source.tree' "$MANIFEST")"
manifest_sbf_sha="$(jq -er '.candidate.sbf_sha256' "$MANIFEST")"
manifest_sbf_bytes="$(jq -er '.candidate.sbf_bytes' "$MANIFEST")"
parity_commit="$(jq -er '.clean_publication_source_build.source_commit' "$PARITY")"
parity_tree="$(jq -er '.clean_publication_source_build.source_tree' "$PARITY")"
parity_sbf_sha="$(jq -er '.clean_publication_source_build.output_sha256' "$PARITY")"
parity_sbf_bytes="$(jq -er '.clean_publication_source_build.output_bytes' "$PARITY")"

[[ "$manifest_commit" == "$FROZEN_SOURCE_COMMIT" ]] || fail "manifest source commit changed"
[[ "$parity_commit" == "$FROZEN_SOURCE_COMMIT" ]] || fail "parity source commit changed"
[[ "$manifest_tree" == "$FROZEN_SOURCE_TREE" ]] || fail "manifest source tree changed"
[[ "$parity_tree" == "$FROZEN_SOURCE_TREE" ]] || fail "parity source tree changed"
[[ "$manifest_sbf_sha" == "$FROZEN_SBF_SHA256" ]] || fail "manifest SBF hash changed"
[[ "$parity_sbf_sha" == "$FROZEN_SBF_SHA256" ]] || fail "parity SBF hash changed"
[[ "$manifest_sbf_bytes" == "$FROZEN_SBF_BYTES" ]] || fail "manifest SBF size changed"
[[ "$parity_sbf_bytes" == "$FROZEN_SBF_BYTES" ]] || fail "parity SBF size changed"

resolved_commit="$(git -C "$ROOT" rev-parse "${FROZEN_SOURCE_COMMIT}^{commit}")"
resolved_tree="$(git -C "$ROOT" rev-parse "${FROZEN_SOURCE_COMMIT}^{tree}")"
[[ "$resolved_commit" == "$FROZEN_SOURCE_COMMIT" ]] || fail "documented source commit is unavailable"
[[ "$resolved_tree" == "$FROZEN_SOURCE_TREE" ]] || fail "documented source tree changed"

git -C "$ROOT" show "$FROZEN_SOURCE_COMMIT:Cargo.toml" \
  | [[ "$(sha_stdin)" == "$FROZEN_CARGO_TOML_SHA256" ]] \
  || fail "documented source Cargo.toml changed"
git -C "$ROOT" show "$FROZEN_SOURCE_COMMIT:Cargo.lock" \
  | [[ "$(sha_stdin)" == "$FROZEN_CARGO_LOCK_SHA256" ]] \
  || fail "documented source Cargo.lock changed"

echo "[3/6] Bind the V5 formal entry points to the documented source"
check_source_sha() {
  local path="$1"
  local expected="$2"
  local actual
  actual="$(git -C "$ROOT" show "$FROZEN_SOURCE_COMMIT:$path" | sha_stdin)"
  [[ "$actual" == "$expected" ]] || fail "formal source identity changed: $path"
}

check_source_sha \
  "aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean" \
  "0b5fe370eba730c48306bf4a25a2c228d8315570b9cabb930b2878604bf3d950"
check_source_sha \
  "aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh" \
  "b65561ceae9fd42ab6a75200bf3f7eb868d8ea00c68703116719bc29dab40c2e"
check_source_sha \
  "aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean" \
  "75b0f3e7ebc3adeb3050be69376d6c07d13aafcef3f9073b5485d6215d457d3a"
check_source_sha \
  "aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/replay-lean432.sh" \
  "22f829f471db3a330ad66afcbeb37d8b4939d6eb96bacae9f4884938f6b7dcfc"
check_source_sha \
  "aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean" \
  "ca7710a24cba91915feb730d0f045fff039fc95cf9c66262144e1211badc81ca"
check_source_sha \
  "aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosureAxiomAudit.lean" \
  "d3d65ea3beb019b2014e0aad301d74f4c0f282b1cf31cb46e4379a0453f2fb1b"

git -C "$ROOT" grep -Fq \
  "theorem current_source_combined_capstone" \
  "$FROZEN_SOURCE_COMMIT" -- \
  "aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean" \
  || fail "combined V5 theorem entry point is missing"
git -C "$ROOT" grep -Fq \
  "theorem tag67AcceptedWireAndVerifierClosure" \
  "$FROZEN_SOURCE_COMMIT" -- \
  "aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean" \
  || fail "Tag-67 verifier theorem entry point is missing"

echo "[4/6] Export the exact clean source tree and fetch its locked dependencies"
source_dir="$tmp/source"
mkdir -p "$source_dir"
git -C "$ROOT" archive "$FROZEN_SOURCE_COMMIT" | tar -x -C "$source_dir"
[[ "$(sha_file "$source_dir/Cargo.toml")" == "$FROZEN_CARGO_TOML_SHA256" ]] \
  || fail "exported Cargo.toml identity changed"
[[ "$(sha_file "$source_dir/Cargo.lock")" == "$FROZEN_CARGO_LOCK_SHA256" ]] \
  || fail "exported Cargo.lock identity changed"
cargo fetch --locked --manifest-path "$source_dir/Cargo.toml" \
  2>&1 | tee "$OUT/cargo-fetch.log"

echo "[5/6] Check the exact SBF toolchain and rebuild"
expected_build_prefix=$'solana-cargo-build-sbf 2.3.0\nplatform-tools v1.48'
expected_build_version="$expected_build_prefix"$'\n''rustc 1.84.1'
reported_build_version="$("$CARGO_BUILD_SBF" --version)"
[[ "$reported_build_version" == "$expected_build_prefix" \
  || "$reported_build_version" == "$expected_build_version" ]] \
  || fail "cargo-build-sbf or platform-tools version differs from the frozen build"
platform_rustc_version="$("$PLATFORM_TOOLS/rust/bin/rustc" --version)"
[[ "$platform_rustc_version" == "rustc 1.84.1-dev" ]] \
  || fail "platform-tools rustc version differs from the frozen build"
actual_build_version="$expected_build_version"
printf '%s\n' "$actual_build_version" > "$OUT/cargo-build-sbf-version.txt"
printf '%s\n' "$platform_rustc_version" > "$OUT/platform-rustc-version.txt"
"$PLATFORM_TOOLS/llvm/bin/clang" --version > "$OUT/platform-clang-version.txt"

mkdir -p "$OUT/sbf" "$tmp/cargo-target" "$tmp/sbf-out"
(
  cd "$source_dir"
  export CARGO_TARGET_DIR="$tmp/cargo-target"
  export NO_DNA=1
  "$CARGO_BUILD_SBF" \
    --manifest-path programs/aspis-verifier/Cargo.toml \
    --arch v0 \
    --offline \
    --skip-tools-install \
    --tools-version v1.48 \
    --sbf-sdk "$SBF_SDK" \
    --sbf-out-dir "$tmp/sbf-out" \
    -- \
    --locked
) 2>&1 | tee "$OUT/sbf-build.log"

built_sbf="$tmp/sbf-out/aspis_verifier.so"
frozen_sbf="$BUNDLE/program/aspis_verifier_v5_tag67.so"
[[ -f "$built_sbf" ]] || fail "cargo-build-sbf did not produce aspis_verifier.so"
[[ "$(wc -c < "$built_sbf" | tr -d ' ')" == "$FROZEN_SBF_BYTES" ]] \
  || fail "rebuilt SBF byte length differs from the frozen artifact"
[[ "$(sha_file "$built_sbf")" == "$FROZEN_SBF_SHA256" ]] \
  || fail "rebuilt SBF hash differs from the frozen artifact"
cmp -s "$built_sbf" "$frozen_sbf" \
  || fail "rebuilt SBF is not byte-for-byte equal to the frozen artifact"
cp "$built_sbf" "$OUT/sbf/aspis_verifier.so"

echo "[6/6] Write the reproducibility record"
jq -n \
  --arg source_commit "$FROZEN_SOURCE_COMMIT" \
  --arg source_tree "$FROZEN_SOURCE_TREE" \
  --arg sbf_sha256 "$FROZEN_SBF_SHA256" \
  --argjson sbf_bytes "$FROZEN_SBF_BYTES" \
  --arg cargo_build_sbf_version "$actual_build_version" \
  '{
    artifact: "aspis_v5_tag67_ci_source_rebuild",
    source_commit: $source_commit,
    source_tree: $source_tree,
    sbf_sha256: $sbf_sha256,
    sbf_bytes: $sbf_bytes,
    byte_equal_to_frozen_candidate: true,
    cargo_build_sbf_version: $cargo_build_sbf_version
  }' > "$OUT/source-rebuild.json"

echo "PASS: frozen V5 SBF rebuilt byte for byte from the documented clean source"
