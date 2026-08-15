#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated"
readonly proof="$bundle/proof"
readonly lean_bin="${LEAN432_BIN:-$(cd "$root/AspisFormal" && elan which lean)}"
readonly aeneas_path="${AENEAS_LEAN_PATH:?set AENEAS_LEAN_PATH to the output of 'lake env printenv LEAN_PATH' in the pinned Aeneas Lean backend}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly aspis_path

found_bridge=0
while IFS= read -r path; do
  if [[ -f "$path/AspisFormal/V5MerkleRustBridge.olean" ]]; then
    found_bridge=1
    break
  fi
done < <(printf '%s' "$aspis_path" | tr ':' '\n')
if [[ $found_bridge -ne 1 ]]; then
  echo "AspisFormal.V5MerkleRustBridge.olean is absent from ASPIS_FORMAL_LEAN_PATH" >&2
  echo "build that single maintained module, then rerun this targeted replay" >&2
  exit 1
fi

if [[ -n "${V5_MERKLE_REPLAY_OUT:-}" ]]; then
  out=$V5_MERKLE_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-merkle-generated.XXXXXX)
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5MerkleDeployedSource"
: > "$log"

export LEAN_PATH="$out:$generated:$proof:$aspis_path:$aeneas_path"

compile() {
  local module_root=$1 target=$2 source=$3
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -R "$module_root" -o "$out/$target.olean" "$source" \
    >> "$log" 2>&1
}

compile "$generated" RuntimeScheduleMerkleReuse \
  "$generated/RuntimeScheduleMerkleReuse.lean"
compile "$generated" V5MerkleDeployedSource/Types \
  "$generated/V5MerkleDeployedSource/Types.lean"
compile "$generated" V5MerkleDeployedSource/FunsExternal \
  "$generated/V5MerkleDeployedSource/FunsExternal.lean"
compile "$generated" V5MerkleDeployedSource/Funs \
  "$generated/V5MerkleDeployedSource/Funs.lean"
compile "$proof" V5MerkleGeneratedDriverInversion \
  "$proof/V5MerkleGeneratedDriverInversion.lean"
compile "$proof" V5MerkleGeneratedDriverBridge \
  "$proof/V5MerkleGeneratedDriverBridge.lean"
compile "$proof" V5MerkleGeneratedHelperBridge \
  "$proof/V5MerkleGeneratedHelperBridge.lean"
compile "$proof" V5MerkleGeneratedRadixBridge \
  "$proof/V5MerkleGeneratedRadixBridge.lean"
compile "$proof" V5MerkleGeneratedSoundnessAdapter \
  "$proof/V5MerkleGeneratedSoundnessAdapter.lean"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' \
    "$proof/V5MerkleGeneratedDriverInversion.lean" \
    "$proof/V5MerkleGeneratedDriverBridge.lean" \
    "$proof/V5MerkleGeneratedHelperBridge.lean" \
    "$proof/V5MerkleGeneratedRadixBridge.lean" \
    "$proof/V5MerkleGeneratedSoundnessAdapter.lean" \
    "$generated/V5MerkleDeployedSource/FunsExternal.lean"; then
  echo "forbidden proof token" >&2
  exit 1
fi

if [[ $(rg -c '^axiom ' "$generated/V5MerkleDeployedSource/FunsExternal.lean") -ne 1 ]] ||
   ! rg -q '^axiom merkle\.fixed_hashv :' \
      "$generated/V5MerkleDeployedSource/FunsExternal.lean"; then
  echo "expected merkle.fixed_hashv to be the sole handwritten external axiom" >&2
  exit 1
fi

if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof shortcut in generated Merkle replay" >&2
  exit 1
fi

echo "Lean 4.32 generated V5 Merkle driver and helper replay: PASS"
echo "V5_MERKLE_REPLAY_OUT=$out"
echo "log: $log"
