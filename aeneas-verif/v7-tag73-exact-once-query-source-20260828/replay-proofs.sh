#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 PINNED_REPO AENEAS_LEAN_BACKEND" >&2
  exit 2
fi

repo=$(realpath "$1")
backend=$(realpath "$2")
bundle="$repo/aeneas-verif/v7-tag73-exact-once-query-source-20260828"
selected=8178d3de1d24d7a3a0102739cb63aca8d7a125a8
user_dir=$(getent passwd "$(id -u)" | cut -d: -f6)
lake_bin=${LAKE_BIN:-"$user_dir/.elan/bin/lake"}
lean_bin=${LEAN_BIN:-"$user_dir/.elan/bin/lean"}

if [[ ! -x "$lake_bin" || ! -x "$lean_bin" ]]; then
  echo "Lean tools not executable; set LAKE_BIN and LEAN_BIN" >&2
  exit 1
fi

if git -C "$repo" rev-parse --git-dir >/dev/null 2>&1; then
  if ! git -C "$repo" merge-base --is-ancestor "$selected" HEAD; then
    echo "selected revision is not an ancestor of HEAD" >&2
    exit 1
  fi
elif [[ "${ASPIS_ALLOW_HASH_ONLY:-0}" != 1 ]]; then
  echo "not a git worktree; set ASPIS_ALLOW_HASH_ONLY=1 for a hashed source snapshot" >&2
  exit 1
fi

(
  cd "$repo"
  sha256sum -c <<'HASHES'
cd652c0fafb7d9a1e0f218e249fa1eea2b4bf6e8f3690053741dd1b005d4c0a8  crates/aspis-core/src/v6_onefold.rs
bf68694e592b0a1f5cd92c341cb1a6a6bb14bdda8726c99168b645d4d7aed608  crates/aspis-core/src/v7_fixed_canonical_audit.rs
dd2f2334ef40be1a3a4648274f23b8ea250c50f08bb06a5e0157f2d941aa5096  programs/aspis-verifier/src/v7_verifier.rs
HASHES
)

(
  cd "$bundle"
  sha256sum -c <<'HASHES'
cf453969d79a026cbc0e14f27807ee9d86040bad27a925ebb07eceabea0f74b5  extraction/direct/V7CanonicalConsumer.llbc
dc8107d4125bef04e1d2d390473b4eeda9864ef912e4437cb1c97626d43de142  extraction/normalized/V7CanonicalConsumerNormalized.llbc
cead19ea307a6206adff11c2aa5714665bbf01a891fa4c19f3cd8ff9309fc399  extraction/parser/V7CanonicalDeferredParser.llbc
HASHES
)

task=$(mktemp -d "$backend/aspis-v7-exact-once-replay.XXXXXX")
cleanup() {
  rm -rf -- "$task"
}
trap cleanup EXIT

python3 "$bundle/source-transform/normalize_gamma_validation.py" \
  "$repo/crates/aspis-core/src/v6_onefold.rs" "$task/v6_onefold.normalized.rs"
printf '%s  %s\n' \
  840bac1f349692ced41a01dbb8ce757ca429c384d8dbbf9eaa7858a11be8551c \
  "$task/v6_onefold.normalized.rs" | sha256sum -c -

cp -R "$bundle/generated/parser/V7CanonicalDeferredParser" "$task/"
cp -R "$bundle/generated/consumer-normalized/V7CanonicalConsumerNormalized" "$task/"
cp "$bundle/proof/V7CanonicalDeferredParserSourceBridge.lean" "$task/"
cp "$bundle/proof/V7CanonicalConsumerSourceBridge.lean" "$task/"

cd "$backend"
lean_path="$task:$($lake_bin env printenv LEAN_PATH)"

env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalDeferredParser/Types.olean" \
  "$task/V7CanonicalDeferredParser/Types.lean"
env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalDeferredParser/FunsExternal.olean" \
  "$task/V7CanonicalDeferredParser/FunsExternal.lean"
env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalDeferredParser/Funs.olean" \
  "$task/V7CanonicalDeferredParser/Funs.lean"
env LEAN_PATH="$lean_path" "$lean_bin" "$task/V7CanonicalDeferredParserSourceBridge.lean"

env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalConsumerNormalized/TypesExternal.olean" \
  "$task/V7CanonicalConsumerNormalized/TypesExternal.lean"
env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalConsumerNormalized/Types.olean" \
  "$task/V7CanonicalConsumerNormalized/Types.lean"
env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalConsumerNormalized/FunsExternal.olean" \
  "$task/V7CanonicalConsumerNormalized/FunsExternal.lean"
env LEAN_PATH="$lean_path" "$lean_bin" -o "$task/V7CanonicalConsumerNormalized/Funs.olean" \
  "$task/V7CanonicalConsumerNormalized/Funs.lean"
env LEAN_PATH="$lean_path" "$lean_bin" "$task/V7CanonicalConsumerSourceBridge.lean"

cd "$repo/AspisFormal"
"$lake_bin" env lean AspisFormal/K1/V7Tag73ExactOnceQueryConsumerBridge.lean
