#!/usr/bin/env bash
set -euo pipefail

readonly RELEASE_TAG="v4.2.0"
readonly RELEASE_COMMIT="ac82b5d438b0c2303dc7169f52c748977713a111"
readonly RELEASE_TREE="f73e1b374fb2cc492783f3c154d0820310329377"
readonly RELEASE_API="https://api.github.com/repos/anza-xyz/agave/releases/tags/$RELEASE_TAG"
readonly TAG_API="https://api.github.com/repos/anza-xyz/agave/git/ref/tags/$RELEASE_TAG"
readonly COMMIT_API="https://api.github.com/repos/anza-xyz/agave/commits/$RELEASE_COMMIT"
readonly ASSET_NAME="solana-release-x86_64-unknown-linux-gnu.tar.bz2"
readonly ASSET_URL="https://github.com/anza-xyz/agave/releases/download/$RELEASE_TAG/$ASSET_NAME"
readonly ASSET_BYTES="86392960"
readonly ASSET_SHA256="1f5eb13bcf3694dbd3cf634602aee5edcf8eab519acac75778391c979c3002b0"
readonly ASSET_ID="505635142"
readonly CHANNEL_NAME="solana-release-x86_64-unknown-linux-gnu.yml"
readonly CHANNEL_URL="https://github.com/anza-xyz/agave/releases/download/$RELEASE_TAG/$CHANNEL_NAME"
readonly CHANNEL_BYTES="98"
readonly CHANNEL_SHA256="76faed5da7a1152d88f37c97c599f2bcccb6912f8596faebd33a5dc70088fc4c"
readonly CHANNEL_ID="505635257"

if [[ $# -ne 1 ]]; then
  echo "usage: $0 <new-task-owned-runtime-root>" >&2
  exit 2
fi

readonly RUNTIME_ROOT=$1
if [[ -z "$RUNTIME_ROOT" || "$RUNTIME_ROOT" != /* || "$RUNTIME_ROOT" == "/" ]]; then
  echo "runtime root must be an explicit absolute non-root path" >&2
  exit 2
fi
if [[ -e "$RUNTIME_ROOT" ]]; then
  echo "refusing to overwrite existing runtime root: $RUNTIME_ROOT" >&2
  exit 2
fi
if [[ "$(uname -s)" != "Linux" || "$(uname -m)" != "x86_64" ]]; then
  echo "official runtime preparation requires Linux x86_64" >&2
  exit 2
fi

for command in awk bzip2 cp curl file find jq ldd readelf rg sha256sum sort stat tar; do
  command -v "$command" >/dev/null || {
    echo "missing required command: $command" >&2
    exit 2
  }
done

readonly DOWNLOAD_DIR="$RUNTIME_ROOT/download"
readonly EXTRACT_DIR="$RUNTIME_ROOT/extracted"
readonly PROVENANCE_DIR="$RUNTIME_ROOT/provenance"
readonly EVIDENCE_DIR="$RUNTIME_ROOT/evidence"
mkdir -p "$DOWNLOAD_DIR" "$EXTRACT_DIR" "$PROVENANCE_DIR" "$EVIDENCE_DIR"

curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "$RELEASE_API" -o "$PROVENANCE_DIR/release-api.json"
curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "$TAG_API" -o "$PROVENANCE_DIR/tag-ref.json"
curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  -H 'Accept: application/vnd.github+json' \
  -H 'X-GitHub-Api-Version: 2022-11-28' \
  "$COMMIT_API" -o "$PROVENANCE_DIR/commit-api.json"

jq -e --arg tag "$RELEASE_TAG" --arg commit "$RELEASE_COMMIT" \
  --arg asset "$ASSET_NAME" --arg asset_sha "sha256:$ASSET_SHA256" \
  --argjson asset_bytes "$ASSET_BYTES" --argjson asset_id "$ASSET_ID" \
  --arg channel "$CHANNEL_NAME" --arg channel_sha "sha256:$CHANNEL_SHA256" \
  --argjson channel_bytes "$CHANNEL_BYTES" --argjson channel_id "$CHANNEL_ID" '
    .tag_name == $tag and .name == "Release v4.2.0" and
    .draft == false and .prerelease == false and
    ([.assets[] | select(
      .id == $asset_id and .name == $asset and .size == $asset_bytes and
      .digest == $asset_sha
    )] | length == 1) and
    ([.assets[] | select(
      .id == $channel_id and .name == $channel and .size == $channel_bytes and
      .digest == $channel_sha
    )] | length == 1)
  ' "$PROVENANCE_DIR/release-api.json" >/dev/null || {
  echo "official release API metadata differs from the frozen release" >&2
  exit 1
}
jq -e --arg tag "refs/tags/$RELEASE_TAG" --arg commit "$RELEASE_COMMIT" '
  .ref == $tag and .object.type == "commit" and .object.sha == $commit
' "$PROVENANCE_DIR/tag-ref.json" >/dev/null || {
  echo "official tag ref differs from the frozen commit" >&2
  exit 1
}
jq -e --arg commit "$RELEASE_COMMIT" --arg tree "$RELEASE_TREE" '
  .sha == $commit and .commit.tree.sha == $tree and
  .commit.verification.verified == true and
  .commit.verification.reason == "valid"
' "$PROVENANCE_DIR/commit-api.json" >/dev/null || {
  echo "official commit verification differs from the frozen release" >&2
  exit 1
}

curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  "$CHANNEL_URL" -o "$DOWNLOAD_DIR/$CHANNEL_NAME"
[[ "$(stat -c '%s' "$DOWNLOAD_DIR/$CHANNEL_NAME")" == "$CHANNEL_BYTES" ]] || {
  echo "official channel manifest has the wrong byte length" >&2
  exit 1
}
[[ "$(sha256sum "$DOWNLOAD_DIR/$CHANNEL_NAME" | awk '{print $1}')" == "$CHANNEL_SHA256" ]] || {
  echo "official channel manifest has the wrong digest" >&2
  exit 1
}
jq -Rn '[inputs | capture("^(?<key>[^:]+): (?<value>.*)$") | {(.key): .value}] | add' \
  <"$DOWNLOAD_DIR/$CHANNEL_NAME" >"$PROVENANCE_DIR/channel.json"
jq -e --arg tag "$RELEASE_TAG" --arg commit "$RELEASE_COMMIT" '
  .channel == $tag and .commit == $commit and .target == "x86_64-unknown-linux-gnu"
' "$PROVENANCE_DIR/channel.json" >/dev/null || {
  echo "official channel manifest content differs from the frozen release" >&2
  exit 1
}

curl --proto '=https' --tlsv1.2 --fail --location --silent --show-error \
  "$ASSET_URL" -o "$DOWNLOAD_DIR/$ASSET_NAME"
[[ "$(stat -c '%s' "$DOWNLOAD_DIR/$ASSET_NAME")" == "$ASSET_BYTES" ]] || {
  echo "official Linux release archive has the wrong byte length" >&2
  exit 1
}
[[ "$(sha256sum "$DOWNLOAD_DIR/$ASSET_NAME" | awk '{print $1}')" == "$ASSET_SHA256" ]] || {
  echo "official Linux release archive has the wrong digest" >&2
  exit 1
}

tar -tjf "$DOWNLOAD_DIR/$ASSET_NAME" >"$EVIDENCE_DIR/archive-members.txt"
if awk 'BEGIN { bad=0 } /^\// { bad=1 } $0 ~ /(^|\/)\.\.($|\/)/ { bad=1 } END { exit bad ? 0 : 1 }' \
  "$EVIDENCE_DIR/archive-members.txt"; then
  echo "official archive contains an unsafe member path" >&2
  exit 1
fi
tar -xjf "$DOWNLOAD_DIR/$ASSET_NAME" -C "$EXTRACT_DIR"

mapfile -t SOLANA_PATHS < <(find "$EXTRACT_DIR" -type f -path '*/bin/solana' -perm -u+x | sort)
mapfile -t VALIDATOR_PATHS < <(find "$EXTRACT_DIR" -type f -path '*/bin/solana-test-validator' -perm -u+x | sort)
if [[ ${#SOLANA_PATHS[@]} -ne 1 || ${#VALIDATOR_PATHS[@]} -ne 1 ]]; then
  echo "release archive must contain exactly one solana and one solana-test-validator" >&2
  exit 1
fi
readonly SOLANA_BIN=${SOLANA_PATHS[0]}
readonly VALIDATOR_BIN=${VALIDATOR_PATHS[0]}
readonly BIN_DIR=$(dirname "$SOLANA_BIN")
[[ "$(dirname "$VALIDATOR_BIN")" == "$BIN_DIR" ]] || {
  echo "required executables do not share one release bin directory" >&2
  exit 1
}

NO_DNA=1 "$SOLANA_BIN" --version >"$EVIDENCE_DIR/solana-version.txt"
NO_DNA=1 "$VALIDATOR_BIN" --version >"$EVIDENCE_DIR/solana-test-validator-version.txt"
rg -q '4\.2\.0.*ac82b5d' "$EVIDENCE_DIR/solana-version.txt" || {
  echo "solana CLI version does not bind Agave v4.2.0/ac82b5d" >&2
  exit 1
}
rg -q '4\.2\.0.*ac82b5d' "$EVIDENCE_DIR/solana-test-validator-version.txt" || {
  echo "test-validator version does not bind Agave v4.2.0/ac82b5d" >&2
  exit 1
}

file "$SOLANA_BIN" "$VALIDATOR_BIN" >"$EVIDENCE_DIR/file.txt"
ldd "$SOLANA_BIN" >"$EVIDENCE_DIR/solana-ldd.txt"
ldd "$VALIDATOR_BIN" >"$EVIDENCE_DIR/solana-test-validator-ldd.txt"
readelf -n "$SOLANA_BIN" >"$EVIDENCE_DIR/solana-notes.txt"
readelf -n "$VALIDATOR_BIN" >"$EVIDENCE_DIR/solana-test-validator-notes.txt"
uname -a >"$EVIDENCE_DIR/uname.txt"
cp /etc/os-release "$EVIDENCE_DIR/os-release.txt"

while IFS= read -r -d '' executable; do
  relative=${executable#"$BIN_DIR/"}
  printf '%s\t%s\t%s\n' \
    "$relative" \
    "$(stat -c '%s' "$executable")" \
    "$(sha256sum "$executable" | awk '{print $1}')"
done < <(find "$BIN_DIR" -maxdepth 1 -type f -perm -u+x -print0 | sort -z) \
  >"$EVIDENCE_DIR/bin-inventory.tsv"

readonly SOLANA_BYTES=$(stat -c '%s' "$SOLANA_BIN")
readonly SOLANA_SHA256=$(sha256sum "$SOLANA_BIN" | awk '{print $1}')
readonly VALIDATOR_BYTES=$(stat -c '%s' "$VALIDATOR_BIN")
readonly VALIDATOR_SHA256=$(sha256sum "$VALIDATOR_BIN" | awk '{print $1}')
readonly BIN_RELATIVE=${BIN_DIR#"$RUNTIME_ROOT/"}
readonly SOLANA_VERSION=$(<"$EVIDENCE_DIR/solana-version.txt")
readonly VALIDATOR_VERSION=$(<"$EVIDENCE_DIR/solana-test-validator-version.txt")

jq -n \
  --arg schema "aspis.v7.agave-runtime-materialization.v1" \
  --arg tag "$RELEASE_TAG" \
  --arg commit "$RELEASE_COMMIT" \
  --arg tree "$RELEASE_TREE" \
  --arg asset "$ASSET_NAME" \
  --arg asset_url "$ASSET_URL" \
  --arg asset_sha "$ASSET_SHA256" \
  --argjson asset_bytes "$ASSET_BYTES" \
  --arg channel "$CHANNEL_NAME" \
  --arg channel_sha "$CHANNEL_SHA256" \
  --arg bin_dir "$BIN_RELATIVE" \
  --arg solana_version "$SOLANA_VERSION" \
  --arg solana_sha "$SOLANA_SHA256" \
  --argjson solana_bytes "$SOLANA_BYTES" \
  --arg validator_version "$VALIDATOR_VERSION" \
  --arg validator_sha "$VALIDATOR_SHA256" \
  --argjson validator_bytes "$VALIDATOR_BYTES" '
    {
      schema: $schema,
      officialRelease: {
        tag: $tag,
        commit: $commit,
        tree: $tree,
        githubCommitVerified: true,
        asset: $asset,
        assetUrl: $asset_url,
        assetSha256: $asset_sha,
        assetBytes: $asset_bytes,
        channelManifest: $channel,
        channelManifestSha256: $channel_sha
      },
      runtime: {
        binDirectoryRelative: $bin_dir,
        solana: {
          version: $solana_version,
          bytes: $solana_bytes,
          sha256: $solana_sha
        },
        solanaTestValidator: {
          version: $validator_version,
          bytes: $validator_bytes,
          sha256: $validator_sha
        }
      },
      downloaded: true,
      builtFromSource: false,
      programDeployed: false,
      transactionSigned: false,
      transactionSubmitted: false
    }
  ' >"$EVIDENCE_DIR/runtime-materialization.json"

(
  cd "$RUNTIME_ROOT"
  sha256sum \
    "download/$CHANNEL_NAME" \
    provenance/channel.json \
    provenance/commit-api.json \
    provenance/release-api.json \
    provenance/tag-ref.json \
    evidence/archive-members.txt \
    evidence/bin-inventory.tsv \
    evidence/file.txt \
    evidence/os-release.txt \
    evidence/runtime-materialization.json \
    evidence/solana-ldd.txt \
    evidence/solana-notes.txt \
    evidence/solana-test-validator-ldd.txt \
    evidence/solana-test-validator-notes.txt \
    evidence/solana-test-validator-version.txt \
    evidence/solana-version.txt \
    evidence/uname.txt \
    >evidence/SHA256SUMS
)

printf '%s\n' "$BIN_DIR" >"$EVIDENCE_DIR/bin-dir.txt"
printf 'Agave runtime materialized: %s\n' "$BIN_DIR"
printf 'solana SHA-256: %s\n' "$SOLANA_SHA256"
printf 'solana-test-validator SHA-256: %s\n' "$VALIDATOR_SHA256"
