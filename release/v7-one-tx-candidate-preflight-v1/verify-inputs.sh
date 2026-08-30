#!/usr/bin/env bash
set -euo pipefail

fail() {
  echo "FAIL: $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "required command is unavailable: $1"
}

for command_name in awk bash find git jq wc; do
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

readonly BUNDLE=$(cd "$(dirname "$0")" && pwd)
readonly ROOT=$(cd "$BUNDLE/../.." && pwd)
readonly MANIFEST="$BUNDLE/manifest.json"
[[ -f "$MANIFEST" ]] || fail "preflight manifest is missing"
git -C "$ROOT" rev-parse --git-dir >/dev/null 2>&1 \
  || fail "preflight bundle is not inside the Aspis git repository"

jq -e '
  .schema == "aspis.v7.one-tx-candidate-preflight.v1" and
  .status == "LINUX_REPRODUCIBLE_SBF_GREEN_AGAVE_AND_POOL_STACK_PENDING" and
  .authorization.build == true and
  .authorization.localSimulationOnly == true and
  .authorization.publicDevnetReadOnlyProbe == true and
  .authorization.sign == false and
  .authorization.submit == false and
  .authorization.deploy == false and
  .authorization.mainnet == false and
  (.programs | length == 2) and
  ([.programs[] | select(.name == "aspis-pool")][0] |
    .expectedBytes == 525888 and
    .expectedSha256 == "82606a25f00fd683b06186cdaae519b52c793d9a2f16f9d3f7c40c2b241685c2" and
    .bindingStatus == "DERIVED_BY_BYTE_IDENTICAL_DA77_DUAL_LINUX_BUILD") and
  ([.programs[] | select(.name == "aspis-verifier")][0] |
    .expectedBytes == 1812264 and
    .expectedSha256 == "c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47" and
    .bindingStatus == "DERIVED_BY_BYTE_IDENTICAL_DA77_DUAL_LINUX_BUILD" and
    .historicalDarwinReference.bytes == 1700384 and
    .historicalDarwinReference.sha256 == "4ee9b4789533e049e2d9e1f43c84fa97f745a98151f9477ebd828de742b75e5c") and
  (.txv1Lifecycle.requiredCases | length) == 11 and
  (.txv1Lifecycle.requiredCases | unique | length) == 11 and
  .txv1Lifecycle.caseBundleIncluded == true and
  .txv1Lifecycle.caseBundlePoolSbfBindingComplete == false and
  .txv1Lifecycle.materializedCaseBundleIncluded == true and
  .txv1Lifecycle.walletPreflightsExecuted == 11 and
  .txv1Lifecycle.agave42AvailableInRecordedLocalEnvironment == false and
  .txv1Lifecycle.suiteExecutedForThisFreeze == false and
  .currentMeasuredCombinedCase.executed == false and
  .currentMeasuredCombinedCase.computeUnits == null and
  .priorMeasuredCombinedCase.currentSource == false
' "$MANIFEST" >/dev/null || fail "manifest schema or fail-closed status changed"

readonly SOURCE_COMMIT=$(jq -er '.source.commit' "$MANIFEST")
readonly SOURCE_TREE=$(jq -er '.source.tree' "$MANIFEST")
readonly CARGO_LOCK_BLOB=$(jq -er '.source.cargoLockBlob' "$MANIFEST")
readonly POOL_TREE=$(jq -er '.source.poolTree' "$MANIFEST")
readonly VERIFIER_TREE=$(jq -er '.source.verifierTree' "$MANIFEST")

[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{commit}")" == "$SOURCE_COMMIT" ]] \
  || fail "frozen source commit is unavailable"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT^{tree}")" == "$SOURCE_TREE" ]] \
  || fail "frozen source tree changed"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:Cargo.lock")" == "$CARGO_LOCK_BLOB" ]] \
  || fail "frozen Cargo.lock blob changed"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-pool")" == "$POOL_TREE" ]] \
  || fail "frozen Pool source tree changed"
[[ "$(git -C "$ROOT" rev-parse "$SOURCE_COMMIT:programs/aspis-verifier")" == "$VERIFIER_TREE" ]] \
  || fail "frozen verifier source tree changed"

while IFS=$'\t' read -r path expected; do
  [[ -n "$path" && "$expected" =~ ^[0-9a-f]{64}$ ]] \
    || fail "malformed source-frozen file entry"
  git -C "$ROOT" cat-file -e "$SOURCE_COMMIT:$path" 2>/dev/null \
    || fail "frozen source omits required path: $path"
  actual=$(git -C "$ROOT" show "$SOURCE_COMMIT:$path" | sha_stdin)
  [[ "$actual" == "$expected" ]] \
    || fail "frozen source file hash changed: $path"
done < <(jq -r '.sourceFrozenFiles[] | [.path, .sha256] | @tsv' "$MANIFEST")

while IFS=$'\t' read -r manifest_path expected; do
  actual=$(git -C "$ROOT" show "$SOURCE_COMMIT:$manifest_path" | sha_stdin)
  [[ "$actual" == "$expected" ]] \
    || fail "program manifest hash changed: $manifest_path"
done < <(jq -r '.programs[] | [.manifest, .manifestSha256] | @tsv' "$MANIFEST")

readonly TOOLCHAIN_PROVENANCE=$(jq -er '.toolchain.frozenInventory.path' "$MANIFEST")
readonly TOOLCHAIN_PROVENANCE_SHA=$(jq -er '.toolchain.frozenInventory.sha256' "$MANIFEST")
readonly TOOLCHAIN_FILE_COUNT=$(jq -er '.toolchain.frozenInventory.toolchainFileCount' "$MANIFEST")
readonly CARGO_BUILD_SBF_SHA=$(jq -er '.toolchain.frozenInventory.cargoBuildSbfSha256' "$MANIFEST")
[[ -f "$ROOT/$TOOLCHAIN_PROVENANCE" ]] \
  || fail "platform-specific frozen toolchain inventory is missing"
toolchain_actual=$(sha_file "$ROOT/$TOOLCHAIN_PROVENANCE")
[[ "$toolchain_actual" == "$TOOLCHAIN_PROVENANCE_SHA" ]] \
  || fail "frozen toolchain inventory hash changed"
jq -e \
  --argjson count "$TOOLCHAIN_FILE_COUNT" \
  --arg cargoBuildSbfSha256 "$CARGO_BUILD_SBF_SHA" '
  .schema == "aspis.v7.linux-x86_64-sbf-toolchain-inventory.v1" and
  .host == "Linux x86_64" and
  (.toolchain_files | length) == $count and
  (.toolchain_files | map(.path) | unique | length) == $count and
  (.toolchain_files | all(
    (.path | type == "string") and
    (.path | startswith("/") | not) and
    (.path | contains("..") | not) and
    (.bytes | type == "number") and .bytes >= 0 and
    (.sha256 | test("^[0-9a-f]{64}$")))) and
  .selection.total == $count and
  .selection.explicit_platform_binaries_and_archives == 11 and
  .selection.complete_sbpf_rust_sysroot_rlibs == 25 and
  .selection.direct_sbf_sdk_release_files == 55 and
  .cargo_build_sbf_sha256 == $cargoBuildSbfSha256 and
  .platform_tools_version == "v1.48" and
  .platform_rustc_version == "rustc 1.84.1-dev" and
  (.cargo_build_sbf_version | startswith("solana-cargo-build-sbf 2.3.0\nplatform-tools v1.48"))
' "$ROOT/$TOOLCHAIN_PROVENANCE" >/dev/null \
  || fail "frozen toolchain inventory contents changed"

readonly CARGO_CACHE_PROVENANCE="$ROOT/$(jq -er '.toolchain.offlineCargoCache.provenancePath' "$MANIFEST")"
readonly CARGO_CACHE_PACKAGES="$ROOT/$(jq -er '.toolchain.offlineCargoCache.packagesPath' "$MANIFEST")"
readonly CARGO_CACHE_INDEX="$ROOT/$(jq -er '.toolchain.offlineCargoCache.indexPath' "$MANIFEST")"
for cache_evidence in "$CARGO_CACHE_PROVENANCE" "$CARGO_CACHE_PACKAGES" "$CARGO_CACHE_INDEX"; do
  [[ -f "$cache_evidence" ]] || fail "offline Cargo cache provenance is incomplete"
done
[[ "$(sha_file "$CARGO_CACHE_PROVENANCE")" == "$(jq -er '.toolchain.offlineCargoCache.provenanceSha256' "$MANIFEST")" ]] \
  || fail "offline Cargo cache provenance hash changed"
[[ "$(sha_file "$CARGO_CACHE_PACKAGES")" == "$(jq -er '.toolchain.offlineCargoCache.packagesSha256' "$MANIFEST")" ]] \
  || fail "offline Cargo package inventory hash changed"
[[ "$(sha_file "$CARGO_CACHE_INDEX")" == "$(jq -er '.toolchain.offlineCargoCache.indexSha256' "$MANIFEST")" ]] \
  || fail "offline Cargo index inventory hash changed"
readonly CARGO_CACHE_PACKAGE_COUNT=$(jq -er '.toolchain.offlineCargoCache.packages' "$MANIFEST")
readonly CARGO_CACHE_INDEX_COUNT=$(jq -er '.toolchain.offlineCargoCache.indexEntries' "$MANIFEST")
[[ "$(wc -l <"$CARGO_CACHE_PACKAGES" | tr -d ' ')" == "$CARGO_CACHE_PACKAGE_COUNT" ]] \
  || fail "offline Cargo package inventory count changed"
[[ "$(wc -l <"$CARGO_CACHE_INDEX" | tr -d ' ')" == "$CARGO_CACHE_INDEX_COUNT" ]] \
  || fail "offline Cargo index inventory count changed"
jq -e \
  --arg packagesSha "$(sha_file "$CARGO_CACHE_PACKAGES")" \
  --arg indexSha "$(sha_file "$CARGO_CACHE_INDEX")" \
  --arg hostCargoSha "$(jq -er '.toolchain.offlineCargoCache.hostCargoSha256' "$MANIFEST")" \
  --arg hostRustcSha "$(jq -er '.toolchain.offlineCargoCache.hostRustcSha256' "$MANIFEST")" \
  --arg hostRustupSha "$(jq -er '.toolchain.offlineCargoCache.hostRustupSha256' "$MANIFEST")" \
  --argjson packages "$CARGO_CACHE_PACKAGE_COUNT" \
  --argjson indexEntries "$CARGO_CACHE_INDEX_COUNT" '
  .schema == "aspis.v7.linux-cargo-offline-cache-provenance.v1" and
  .cargoLockSha256 == "25cae3f276bd5831785bdb25e204ce99213934e7fcec3f5a76a5d742a018426b" and
  .hostCargo.sha256 == $hostCargoSha and
  .hostCargo.version == "cargo 1.94.1 (29ea6fb6a 2026-03-24)" and
  .hostRustc.sha256 == $hostRustcSha and
  .hostRustc.version == "rustc 1.94.1 (e408947bf 2026-03-25)" and
  .hostRustup.sha256 == $hostRustupSha and
  .hostRustup.version == "rustup 1.29.0 (28d1352db 2026-03-05)" and
  .hostRustup.bytes == 20838840 and
  .packages.count == $packages and .packages.inventorySha256 == $packagesSha and
  .sparseIndex.entries == $indexEntries and .sparseIndex.inventorySha256 == $indexSha and
  .networkAllowed == false and .downloadsPerformed == false and
  .sharedCacheMutationAuthorized == false
' "$CARGO_CACHE_PROVENANCE" >/dev/null \
  || fail "offline Cargo cache provenance contents changed"
while IFS=$'\t' read -r name version source archive_path archive_bytes archive_sha \
    source_path source_files source_identity; do
  [[ -n "$name" && -n "$version" && "$source" == "registry+https://github.com/rust-lang/crates.io-index" ]] \
    || fail "malformed offline Cargo package identity"
  [[ "$archive_path" != /* && "$archive_path" != *..* && "$source_path" != /* && "$source_path" != *..* ]] \
    || fail "unsafe offline Cargo cache path"
  [[ "$archive_bytes" =~ ^[0-9]+$ && "$archive_sha" =~ ^[0-9a-f]{64}$ && "$source_files" =~ ^[0-9]+$ \
      && "$source_identity" =~ ^[0-9]+:[0-9a-f]{64}$ ]] \
    || fail "malformed offline Cargo package checksum"
done <"$CARGO_CACHE_PACKAGES"
while IFS=$'\t' read -r index_path index_bytes index_sha; do
  [[ "$index_path" != /* && "$index_path" != *..* && "$index_bytes" =~ ^[0-9]+$ \
      && "$index_sha" =~ ^[0-9a-f]{64}$ ]] \
    || fail "malformed offline Cargo index entry"
done <"$CARGO_CACHE_INDEX"

readonly SBF_CARGO_CACHE_PROVENANCE="$ROOT/$(jq -er '.toolchain.offlineCargoCache.sbfProvenancePath' "$MANIFEST")"
readonly SBF_CARGO_CACHE_PACKAGES="$ROOT/$(jq -er '.toolchain.offlineCargoCache.sbfPackagesPath' "$MANIFEST")"
readonly SBF_CARGO_CACHE_INDEX="$ROOT/$(jq -er '.toolchain.offlineCargoCache.sbfIndexPath' "$MANIFEST")"
for cache_evidence in "$SBF_CARGO_CACHE_PROVENANCE" "$SBF_CARGO_CACHE_PACKAGES" "$SBF_CARGO_CACHE_INDEX"; do
  [[ -f "$cache_evidence" ]] || fail "cargo +solana offline cache provenance is incomplete"
done
[[ "$(sha_file "$SBF_CARGO_CACHE_PROVENANCE")" == "$(jq -er '.toolchain.offlineCargoCache.sbfProvenanceSha256' "$MANIFEST")" ]] \
  || fail "cargo +solana cache provenance hash changed"
[[ "$(sha_file "$SBF_CARGO_CACHE_PACKAGES")" == "$(jq -er '.toolchain.offlineCargoCache.sbfPackagesSha256' "$MANIFEST")" ]] \
  || fail "cargo +solana package inventory hash changed"
[[ "$(sha_file "$SBF_CARGO_CACHE_INDEX")" == "$(jq -er '.toolchain.offlineCargoCache.sbfIndexSha256' "$MANIFEST")" ]] \
  || fail "cargo +solana index inventory hash changed"
readonly SBF_CARGO_CACHE_PACKAGE_COUNT=$(jq -er '.toolchain.offlineCargoCache.sbfPackages' "$MANIFEST")
readonly SBF_CARGO_CACHE_INDEX_COUNT=$(jq -er '.toolchain.offlineCargoCache.sbfIndexEntries' "$MANIFEST")
[[ "$(wc -l <"$SBF_CARGO_CACHE_PACKAGES" | tr -d ' ')" == "$SBF_CARGO_CACHE_PACKAGE_COUNT" ]] \
  || fail "cargo +solana package inventory count changed"
[[ "$(wc -l <"$SBF_CARGO_CACHE_INDEX" | tr -d ' ')" == "$SBF_CARGO_CACHE_INDEX_COUNT" ]] \
  || fail "cargo +solana index inventory count changed"
jq -e \
  --arg packagesSha "$(sha_file "$SBF_CARGO_CACHE_PACKAGES")" \
  --arg indexSha "$(sha_file "$SBF_CARGO_CACHE_INDEX")" \
  --arg platformCargoSha "$(jq -er '.toolchain_files[] | select(.path == "platform-tools-v1.48/rust/bin/cargo") | .sha256' "$ROOT/$TOOLCHAIN_PROVENANCE")" \
  --argjson packages "$SBF_CARGO_CACHE_PACKAGE_COUNT" \
  --argjson indexEntries "$SBF_CARGO_CACHE_INDEX_COUNT" '
  .schema == "aspis.v7.linux-sbf-cargo-offline-cache-provenance.v1" and
  .cargoLockSha256 == "25cae3f276bd5831785bdb25e204ce99213934e7fcec3f5a76a5d742a018426b" and
  .registryNamespace == "index.crates.io-6f17d22bba15001f" and
  .platformCargo.version == "cargo 1.84.0 (12fe57a9d 2025-04-07)" and
  .platformCargo.sha256 == $platformCargoSha and
  .packages.count == $packages and .packages.inventorySha256 == $packagesSha and
  .index.entries == $indexEntries and .index.inventorySha256 == $indexSha and
  .observedBuild.poolSha256 == "82606a25f00fd683b06186cdaae519b52c793d9a2f16f9d3f7c40c2b241685c2" and
  .observedBuild.verifierSha256 == "c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47" and
  .observedBuild.aAndBByteIdentical == true and
  .observedBuild.memorySwapPeakBytes == 0 and
  .networkAllowed == false and .downloadsPerformed == false and
  .sharedCacheMutationAuthorized == false
' "$SBF_CARGO_CACHE_PROVENANCE" >/dev/null \
  || fail "cargo +solana cache provenance contents changed"
while IFS=$'\t' read -r name version source archive_path archive_bytes archive_sha \
    source_path source_files source_identity; do
  [[ -n "$name" && -n "$version" && "$source" == "registry+https://github.com/rust-lang/crates.io-index" ]] \
    || fail "malformed cargo +solana package identity"
  [[ "$archive_path" != /* && "$archive_path" != *..* && "$source_path" != /* && "$source_path" != *..* ]] \
    || fail "unsafe cargo +solana cache path"
  [[ "$archive_bytes" =~ ^[0-9]+$ && "$archive_sha" =~ ^[0-9a-f]{64}$ && "$source_files" =~ ^[0-9]+$ \
      && "$source_identity" =~ ^[0-9]+:[0-9a-f]{64}$ ]] \
    || fail "malformed cargo +solana package checksum"
done <"$SBF_CARGO_CACHE_PACKAGES"
while IFS=$'\t' read -r index_path index_bytes index_sha; do
  [[ "$index_path" != /* && "$index_path" != *..* && "$index_bytes" =~ ^[0-9]+$ \
      && "$index_sha" =~ ^[0-9a-f]{64}$ ]] \
    || fail "malformed cargo +solana index entry"
done <"$SBF_CARGO_CACHE_INDEX"

while IFS=$'\t' read -r path expected; do
  [[ -n "$path" && "$expected" =~ ^[0-9a-f]{64}$ ]] \
    || fail "malformed release-harness file entry: $path"
  [[ -f "$ROOT/$path" ]] || fail "release-harness file is missing: $path"
  [[ "$(sha_file "$ROOT/$path")" == "$expected" ]] \
    || fail "release-harness file hash changed: $path"
done < <(jq -r '.releaseHarnessFiles[] | [.path, .sha256] | @tsv' "$MANIFEST")

readonly VERIFIER_SHA=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedSha256' "$MANIFEST")
readonly VERIFIER_BYTES=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .expectedBytes' "$MANIFEST")
readonly HISTORICAL_VERIFIER_ARTIFACT=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .historicalDarwinReference.artifact' "$MANIFEST")
readonly HISTORICAL_VERIFIER_SHA=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .historicalDarwinReference.sha256' "$MANIFEST")
readonly HISTORICAL_VERIFIER_BYTES=$(jq -er '.programs[] | select(.name == "aspis-verifier") | .historicalDarwinReference.bytes' "$MANIFEST")
[[ "$(git -C "$ROOT" show "$SOURCE_COMMIT:$HISTORICAL_VERIFIER_ARTIFACT" | sha_stdin)" == "$HISTORICAL_VERIFIER_SHA" ]] \
  || fail "historical Darwin verifier artifact hash changed"
[[ "$(git -C "$ROOT" cat-file -s "$SOURCE_COMMIT:$HISTORICAL_VERIFIER_ARTIFACT")" == "$HISTORICAL_VERIFIER_BYTES" ]] \
  || fail "historical Darwin verifier artifact length changed"

while IFS=$'\t' read -r name artifact expected_bytes expected_sha checked_in; do
  [[ "$checked_in" == "true" && -f "$ROOT/$artifact" ]] \
    || fail "Linux SBF reference artifact is not checked in: $name"
  [[ "$(wc -c <"$ROOT/$artifact" | tr -d ' ')" == "$expected_bytes" ]] \
    || fail "Linux SBF reference artifact length changed: $name"
  [[ "$(sha_file "$ROOT/$artifact")" == "$expected_sha" ]] \
    || fail "Linux SBF reference artifact hash changed: $name"
done < <(jq -r '.programs[] | [.name, .referenceArtifact, .expectedBytes, .expectedSha256,
  .referenceArtifactCheckedIn] | @tsv' "$MANIFEST")

readonly REPRODUCIBLE_SBF_RECORD="$ROOT/$(jq -er '.linuxSbfConfirmation.reproducibleSbfRecord' "$MANIFEST")"
[[ -f "$REPRODUCIBLE_SBF_RECORD" ]] || fail "reproducible SBF record is missing"
[[ "$(sha_file "$REPRODUCIBLE_SBF_RECORD")" == "$(jq -er '.linuxSbfConfirmation.reproducibleSbfRecordSha256' "$MANIFEST")" ]] \
  || fail "reproducible SBF record hash changed"
jq -e \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg poolSha "$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedSha256' "$MANIFEST")" \
  --arg verifierSha "$VERIFIER_SHA" \
  --arg hostCache "$(jq -er '.toolchain.offlineCargoCache.provenanceSha256' "$MANIFEST")" \
  --arg sbfCache "$(jq -er '.toolchain.offlineCargoCache.sbfProvenanceSha256' "$MANIFEST")" '
  .schema == "aspis.v7.one-tx-reproducible-sbf.v2" and
  .source.commit == $sourceCommit and .source.independentCopies == 2 and
  .source.archivesByteIdentical == true and
  .builder.offlineCargoCacheProvenanceSha256 == $hostCache and
  .builder.offlineCargoCacheVerifiedBeforeAndAfter == true and
  .builder.offlineSbfCargoCacheProvenanceSha256 == $sbfCache and
  .builder.offlineSbfCargoCacheVerifiedBeforeAndAfter == true and
  .builder.memorySwapMaxBytes == 0 and
  .programs.pool.sha256 == $poolSha and .programs.pool.buildsByteIdentical == true and
  .programs.verifier.sha256 == $verifierSha and .programs.verifier.buildsByteIdentical == true and
  .signed == false and .submitted == false and .deployed == false
' "$REPRODUCIBLE_SBF_RECORD" >/dev/null || fail "reproducible SBF record contents changed"

readonly CASE_BUNDLE_RELATIVE=$(jq -er '.txv1Lifecycle.caseBundle' "$MANIFEST")
readonly CASE_BUNDLE="$ROOT/$CASE_BUNDLE_RELATIVE"
readonly CASE_BUNDLE_SHA=$(jq -er '.txv1Lifecycle.caseBundleSha256' "$MANIFEST")
readonly CASE_INVENTORY_SHA=$(jq -er '.txv1Lifecycle.caseBundleInventorySha256' "$MANIFEST")
readonly OFFLINE_AUDIT_RELATIVE=$(jq -er '.txv1Lifecycle.caseBundleOfflineAudit' "$MANIFEST")
readonly OFFLINE_AUDIT="$ROOT/$OFFLINE_AUDIT_RELATIVE"
readonly OFFLINE_AUDIT_SHA=$(jq -er '.txv1Lifecycle.caseBundleOfflineAuditSha256' "$MANIFEST")
readonly BUNDLE_VERIFY="$ROOT/scripts/v7_txv1_bundle_verify.sh"
[[ -d "$CASE_BUNDLE" && -x "$BUNDLE_VERIFY" && -f "$OFFLINE_AUDIT" ]] \
  || fail "deterministic bundle, validator, or offline audit is missing"
[[ "$(sha_file "$CASE_BUNDLE/bundle.json")" == "$CASE_BUNDLE_SHA" ]] \
  || fail "case bundle manifest hash changed"
[[ "$(sha_file "$CASE_BUNDLE/TEMPLATE-SHA256SUMS")" == "$CASE_INVENTORY_SHA" ]] \
  || fail "case bundle checksum inventory changed"
[[ "$(sha_file "$OFFLINE_AUDIT")" == "$OFFLINE_AUDIT_SHA" ]] \
  || fail "offline audit hash changed"

bundle_file_count=0
bundle_bytes=0
while IFS= read -r -d '' file; do
  ((bundle_file_count += 1))
  bytes=$(wc -c <"$file" | tr -d ' ')
  ((bundle_bytes += bytes))
done < <(find "$CASE_BUNDLE" -type f -print0)
[[ "$bundle_file_count" == "$(jq -er '.txv1Lifecycle.caseBundleFiles' "$MANIFEST")" ]] \
  || fail "case bundle file count changed"
[[ "$bundle_bytes" == "$(jq -er '.txv1Lifecycle.caseBundleBytes' "$MANIFEST")" ]] \
  || fail "case bundle byte count changed"

bundle_audit=$($BUNDLE_VERIFY "$CASE_BUNDLE")
jq -e \
  --arg bundleSha "$CASE_BUNDLE_SHA" \
  --arg inventorySha "$CASE_INVENTORY_SHA" '
  .schema == "aspis.v7.deterministic-agave-bundle-offline-audit.v1" and
  .cases == 11 and .exactRequiredCaseSet == true and
  .allNegativeCasesRequireRollback == true and
  .hashesAndLengthsMatch == true and
  .canonicalAsq8InputsMatch == true and
  .deterministicTokenFailureTestDoublePinned == true and
  .bundleSha256 == $bundleSha and
  .templateInventorySha256 == $inventorySha and
  .sbfMaterializedAndMatched == false and
  .agaveExecutionPerformed == false and
  .signed == false and .submitted == false and .deployed == false
' <<<"$bundle_audit" >/dev/null || fail "offline bundle validator did not reproduce the frozen result"

readonly MATERIALIZED_BUNDLE_RELATIVE=$(jq -er '.txv1Lifecycle.materializedCaseBundle' "$MANIFEST")
readonly MATERIALIZED_BUNDLE="$ROOT/$MATERIALIZED_BUNDLE_RELATIVE"
[[ -d "$MATERIALIZED_BUNDLE" ]] || fail "materialized eleven-case bundle is missing"
[[ "$(sha_file "$MATERIALIZED_BUNDLE/bundle.json")" == "$(jq -er '.txv1Lifecycle.materializedCaseBundleSha256' "$MANIFEST")" ]] \
  || fail "materialized bundle hash changed"
[[ "$(sha_file "$MATERIALIZED_BUNDLE/TEMPLATE-SHA256SUMS")" == "$(jq -er '.txv1Lifecycle.materializedCaseBundleInventorySha256' "$MANIFEST")" ]] \
  || fail "materialized bundle inventory hash changed"
materialized_bundle_audit=$($BUNDLE_VERIFY "$MATERIALIZED_BUNDLE" --materialized)
[[ "$(sha_stdin <<<"$materialized_bundle_audit")" == "$(jq -er '.txv1Lifecycle.materializedCaseBundleOfflineAuditSha256' "$MANIFEST")" ]] \
  || fail "materialized bundle audit hash changed"
jq -e '
  .schema == "aspis.v7.deterministic-agave-bundle-offline-audit.v1" and
  .cases == 11 and .exactRequiredCaseSet == true and
  .allNegativeCasesRequireRollback == true and
  .hashesAndLengthsMatch == true and .canonicalAsq8InputsMatch == true and
  .deterministicTokenFailureTestDoublePinned == true and
  .sbfMaterializedAndMatched == true and .agaveExecutionPerformed == false and
  .signed == false and .submitted == false and .deployed == false
' <<<"$materialized_bundle_audit" >/dev/null || fail "materialized bundle validation changed"

jq -e \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$SOURCE_TREE" \
  --arg poolTree "$POOL_TREE" \
  --arg verifierTree "$VERIFIER_TREE" \
  --arg bundleSha "$CASE_BUNDLE_SHA" \
  --arg inventorySha "$CASE_INVENTORY_SHA" '
  .schema == "aspis.v7.deterministic-agave-bundle-offline-audit.v2" and
  .programSource.commit == $sourceCommit and
  .programSource.tree == $sourceTree and
  .programSource.poolTree == $poolTree and
  .programSource.verifierTree == $verifierTree and
  .bundle.bundleSha256 == $bundleSha and
  .bundle.templateInventorySha256 == $inventorySha and
  .bundle.cases == 11 and .bundle.successCases == 4 and .bundle.rollbackCases == 7 and
  .bundle.allNegativeCasesRequireRollback == true and
  .bundle.independentGenerations == 2 and
  .bundle.independentOutputsByteIdentical == true and
  .txv1.walletPreflightsExecuted == 11 and .txv1.allPreflightsPassed == true and
  ([.txv1.shapes[].serializedTransactionBytes] == [833, 866, 998, 1031]) and
  .sbf.poolBindingComplete == false and .sbf.poolSha256 == null and .sbf.poolBytes == null and
  .execution.agaveSuiteExecuted == false and
  .execution.liteSvmSubstituted == false and
  .execution.componentSumsSubstituted == false and
  .execution.signed == false and .execution.submitted == false and .execution.deployed == false and
  .result == "OFFLINE_FIXTURES_GREEN_RUNTIME_PENDING"
' "$OFFLINE_AUDIT" >/dev/null || fail "offline evidence record changed"

while IFS= read -r script_path; do
  bash -n "$ROOT/$script_path" || fail "shell syntax check failed: $script_path"
done < <(jq -r '.releaseHarnessFiles[] | select(.path | endswith(".sh")) | .path' "$MANIFEST")
bash -n "$BUNDLE/verify-inputs.sh" || fail "shell syntax check failed: release verifier"

jq -n \
  --arg sourceCommit "$SOURCE_COMMIT" \
  --arg sourceTree "$SOURCE_TREE" \
  --arg verifierSha256 "$VERIFIER_SHA" \
  --arg historicalVerifierSha256 "$HISTORICAL_VERIFIER_SHA" \
  --arg poolSha256 "$(jq -er '.programs[] | select(.name == "aspis-pool") | .expectedSha256' "$MANIFEST")" \
  --arg bundleSha256 "$CASE_BUNDLE_SHA" \
  --arg bundleInventorySha256 "$CASE_INVENTORY_SHA" \
  --arg offlineAuditSha256 "$OFFLINE_AUDIT_SHA" \
  --arg toolchainInventorySha256 "$TOOLCHAIN_PROVENANCE_SHA" \
  --arg cargoCacheProvenanceSha256 "$(sha_file "$CARGO_CACHE_PROVENANCE")" \
  --arg cargoCachePackagesSha256 "$(sha_file "$CARGO_CACHE_PACKAGES")" \
  --arg cargoCacheIndexSha256 "$(sha_file "$CARGO_CACHE_INDEX")" \
  --arg sbfCargoCacheProvenanceSha256 "$(sha_file "$SBF_CARGO_CACHE_PROVENANCE")" \
  --arg sbfCargoCachePackagesSha256 "$(sha_file "$SBF_CARGO_CACHE_PACKAGES")" \
  --arg sbfCargoCacheIndexSha256 "$(sha_file "$SBF_CARGO_CACHE_INDEX")" '
  {
    schema: "aspis.v7.one-tx-candidate-input-audit.v2",
    sourceCommit: $sourceCommit,
    sourceTree: $sourceTree,
    frozenSourceFileHashesMatch: true,
    frozenReleaseHarnessHashesMatch: true,
    frozenToolchainInventoryMatches: true,
    programFeatureManifestsMatch: true,
    verifierLinuxReference: {bytes: 1812264, sha256: $verifierSha256},
    verifierHistoricalDarwinReference: {bytes: 1700384, sha256: $historicalVerifierSha256},
    poolReference: {
      bytes: 525888,
      sha256: $poolSha256,
      status: "DERIVED_BY_BYTE_IDENTICAL_DA77_DUAL_LINUX_BUILD"
    },
    deterministicCaseBundle: {
      cases: 11,
      successCases: 4,
      rollbackCases: 7,
      allNegativeCasesRequireRollback: true,
      bundleSha256: $bundleSha256,
      inventorySha256: $bundleInventorySha256,
      offlineAuditSha256: $offlineAuditSha256,
      independentGenerationsByteIdentical: true,
      walletPreflightsPassed: 11,
      sbfMaterialized: true,
      materializedBundleSha256: "b4ca543d65a3f12abff72aa412bcad77acb7fb335692c045db2356f4230eda7f",
      materializedBundleAuditSha256: "206e1237b8a49725ea6ad03b1878e3604ef460c3a9f0477d4c91f65e861a1569",
      agaveExecuted: false
    },
    derivationDualBuildExecuted: true,
    provenanceCompleteConfirmationReplayExecuted: true,
    reproducibleSbfRecordSha256: "1b66865f8b7f9a9ec7158b92fc0e526f7ac37713282c28a82f2452fe23596aab",
    poolCheckpointStackGate: {
      status: "MAINNET_BLOCKER",
      function: "aspis_pool::pair_forest::plan_pair_forest_checkpoint_accounts_v1",
      stackOffsetBytes: 4368,
      maximumOffsetBytes: 4096
    },
    disposableAgaveSuiteExecuted: false,
    publicDevnetTransactionSigned: false,
    publicDevnetTransactionSubmitted: false,
    releaseReady: false,
    remainingGates: [
      "reduce the production permissionless-checkpoint SBF stack frame below 4096 bytes and refresh the Pool SBF evidence",
      "execute all eleven cases on a disposable Agave 4.2+ validator",
      "measure fresh combined CU for all four honest paths and enforce rollback for all seven failures",
      "public-devnet TxV1 execution activation before any public RPC simulation"
    ],
    toolchainInventorySha256: $toolchainInventorySha256,
    offlineCargoCache: {
      provenanceSha256: $cargoCacheProvenanceSha256,
      packageInventorySha256: $cargoCachePackagesSha256,
      indexInventorySha256: $cargoCacheIndexSha256,
      packages: 428,
      indexEntries: 395,
      cargoPlusSolana: {
        provenanceSha256: $sbfCargoCacheProvenanceSha256,
        packageInventorySha256: $sbfCargoCachePackagesSha256,
        indexInventorySha256: $sbfCargoCacheIndexSha256,
        packages: 186,
        indexEntries: 399
      },
      buildTimeByteVerificationRequired: true
    },
    signed: false,
    submitted: false,
    deployed: false
  }'
