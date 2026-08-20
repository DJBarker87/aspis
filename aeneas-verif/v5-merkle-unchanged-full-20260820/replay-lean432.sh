#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly generated="$bundle/generated"
readonly proof="$bundle/proof"
readonly old_generated="$root/aeneas-verif/v5-merkle-deployed-source-20260815/generated"
readonly lean_bin="${LEAN432_BIN:-$(cd "$root/AspisFormal" && elan which lean)}"
readonly aeneas_path="${AENEAS_LEAN_PATH:?set AENEAS_LEAN_PATH to the pinned Aeneas Lean backend build path}"

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

aspis_path=${ASPIS_FORMAL_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
readonly aspis_path

if [[ -n "${V5_MERKLE_EXTERNALS_OUT:-}" ]]; then
  out=$V5_MERKLE_EXTERNALS_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d "${TMPDIR:-/tmp}/v5-merkle-externals.XXXXXX")
fi
readonly out
readonly log="$out/lean432.log"
mkdir -p "$out/V5MerkleUnchangedFull" "$out/proof"
: > "$log"

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

scan() {
  local pattern=$1
  shift
  if command -v rg >/dev/null 2>&1; then
    rg -n "$pattern" "$@"
  else
    grep -En "$pattern" "$@"
  fi
}

[[ $(sha256 "$generated/V5MerkleUnchangedFull/Types.lean") == \
  1179f5c160138711a16285e8fdcc0b4b93aeb7ac98135157b8839c31c6170437 ]]
[[ $(sha256 "$generated/V5MerkleUnchangedFull/Funs.lean") == \
  7f89a145aef6103bdb7238f94ac72b56e5cbcfd21ad4a1634bae2b94a17d4c38 ]]
[[ $(sha256 "$generated/V5MerkleUnchangedFull/TypesExternalRaw.lean.txt") == \
  bba20f3dd60edb17b0722f48b89185216e8be4dcf5b0c6181af21f8127ddf3e9 ]]
[[ $(sha256 "$generated/V5MerkleUnchangedFull/FunsExternalRaw.lean.txt") == \
  ba0d9ca8b931467748335d921e0478066e42a0eab5b1cb95b8e209f6ab5cfee1 ]]
[[ $(sha256 "$bundle/translation.json") == \
  4a56aaaf8071b598bab4b49289849e3a9da5d663a5104c36b541572d5788e557 ]]

export LEAN_PATH="$out:$generated:$old_generated:$proof:$aspis_path:$aeneas_path"

compile() {
  local module_root=$1 target=$2 source=$3
  echo "COMPILE $target" >> "$log"
  "$lean_bin" -j 1 -R "$module_root" -o "$out/$target.olean" "$source" \
    >> "$log" 2>&1
}

compile "$old_generated" RuntimeScheduleMerkleReuse \
  "$old_generated/RuntimeScheduleMerkleReuse.lean"
compile "$proof" V5MerkleQueryReuseProof \
  "$proof/V5MerkleQueryReuseProof.lean"
compile "$generated" V5MerkleUnchangedFull/TypesExternal \
  "$generated/V5MerkleUnchangedFull/TypesExternal.lean"
compile "$generated" V5MerkleUnchangedFull/Types \
  "$generated/V5MerkleUnchangedFull/Types.lean"
compile "$generated" V5MerkleUnchangedFull/FunsExternal \
  "$generated/V5MerkleUnchangedFull/FunsExternal.lean"
compile "$generated" V5MerkleUnchangedFull/Funs \
  "$generated/V5MerkleUnchangedFull/Funs.lean"
compile "$proof" V5MerkleExternalSemantics \
  "$proof/V5MerkleExternalSemantics.lean"
compile "$proof" V5MerkleUnchangedFullParserBridge \
  "$proof/V5MerkleUnchangedFullParserBridge.lean"
compile "$proof" V5MerkleUnchangedFullHelperBridge \
  "$proof/V5MerkleUnchangedFullHelperBridge.lean"
compile "$proof" V5MerkleUnchangedFullLeafBridge \
  "$proof/V5MerkleUnchangedFullLeafBridge.lean"
compile "$proof" V5MerkleUnchangedFullRadixCompat \
  "$proof/V5MerkleUnchangedFullRadixCompat.lean"
compile "$proof" V5MerkleUnchangedFullRadixInversion \
  "$proof/V5MerkleUnchangedFullRadixInversion.lean"
compile "$proof" V5MerkleUnchangedFullRadixSoundness \
  "$proof/V5MerkleUnchangedFullRadixSoundness.lean"
compile "$proof" V5MerkleUnchangedFullHelperSoundness \
  "$proof/V5MerkleUnchangedFullHelperSoundness.lean"
compile "$proof" V5MerkleTopologyConstructorModel \
  "$proof/V5MerkleTopologyConstructorModel.lean"
compile "$proof" V5MerkleUnchangedFullConstructorSemantics \
  "$proof/V5MerkleUnchangedFullConstructorSemantics.lean"
compile "$proof" V5MerkleUnchangedFullRecordChunks \
  "$proof/V5MerkleUnchangedFullRecordChunks.lean"
compile "$proof" V5MerkleUnchangedFullLeafTraceLists \
  "$proof/V5MerkleUnchangedFullLeafTraceLists.lean"
compile "$proof" V5MerkleUnchangedFullWireCanonicality \
  "$proof/V5MerkleUnchangedFullWireCanonicality.lean"
compile "$proof" V5MerkleUnchangedFullFrontierChunks \
  "$proof/V5MerkleUnchangedFullFrontierChunks.lean"
compile "$proof" V5MerkleUnchangedFullParserBounds \
  "$proof/V5MerkleUnchangedFullParserBounds.lean"
compile "$proof" V5MerkleUnchangedFullLeafTable \
  "$proof/V5MerkleUnchangedFullLeafTable.lean"
compile "$proof" V5MerkleUnchangedFullWireTable \
  "$proof/V5MerkleUnchangedFullWireTable.lean"
compile "$proof" V5MerkleUnchangedFullSectionBase \
  "$proof/V5MerkleUnchangedFullSectionBase.lean"
compile "$proof" V5MerkleUnchangedFullTopologyAccessors \
  "$proof/V5MerkleUnchangedFullTopologyAccessors.lean"
compile "$proof" V5MerkleUnchangedFullOrderedChildPositions \
  "$proof/V5MerkleUnchangedFullOrderedChildPositions.lean"
compile "$proof" V5MerkleUnchangedFullGroupTraceLists \
  "$proof/V5MerkleUnchangedFullGroupTraceLists.lean"
compile "$proof" V5MerkleUnchangedFullGroupCursorPrefixes \
  "$proof/V5MerkleUnchangedFullGroupCursorPrefixes.lean"
compile "$proof" V5MerkleUnchangedFullLevelTraceLists \
  "$proof/V5MerkleUnchangedFullLevelTraceLists.lean"
compile "$proof" V5MerkleUnchangedFullMaskSemantics \
  "$proof/V5MerkleUnchangedFullMaskSemantics.lean"
compile "$proof" V5MerkleUnchangedFullMaskCounts \
  "$proof/V5MerkleUnchangedFullMaskCounts.lean"
compile "$proof" V5MerkleUnchangedFullSectionTopologyAlignment \
  "$proof/V5MerkleUnchangedFullSectionTopologyAlignment.lean"
compile "$proof" V5MerkleUnchangedQueryModelBridge \
  "$proof/V5MerkleUnchangedQueryModelBridge.lean"
compile "$proof" V5MerkleUnchangedFullSectionChildOrder \
  "$proof/V5MerkleUnchangedFullSectionChildOrder.lean"
compile "$proof" V5MerkleUnchangedFullFrontierPositionUniqueness \
  "$proof/V5MerkleUnchangedFullFrontierPositionUniqueness.lean"
compile "$proof" V5MerkleUnchangedFullCanonicalNodeTable \
  "$proof/V5MerkleUnchangedFullCanonicalNodeTable.lean"
compile "$proof" V5MerkleUnchangedFullGroupParentAlignment \
  "$proof/V5MerkleUnchangedFullGroupParentAlignment.lean"
compile "$proof" V5MerkleUnchangedFullGroupChildSources \
  "$proof/V5MerkleUnchangedFullGroupChildSources.lean"
compile "$proof" V5MerkleUnchangedFullLevelChildSources \
  "$proof/V5MerkleUnchangedFullLevelChildSources.lean"
compile "$proof" V5MerkleUnchangedFullCanonicalChildSources \
  "$proof/V5MerkleUnchangedFullCanonicalChildSources.lean"
compile "$proof" V5MerkleUnchangedFullCanonicalLevelStep \
  "$proof/V5MerkleUnchangedFullCanonicalLevelStep.lean"
compile "$proof" V5MerkleUnchangedFullMatchedSuffixShape \
  "$proof/V5MerkleUnchangedFullMatchedSuffixShape.lean"
compile "$proof" V5MerkleUnchangedFullReleasedLevelSources \
  "$proof/V5MerkleUnchangedFullReleasedLevelSources.lean"
compile "$proof" V5MerkleUnchangedFullCanonicalLevelInduction \
  "$proof/V5MerkleUnchangedFullCanonicalLevelInduction.lean"
compile "$proof" V5MerkleUnchangedFullBinaryCapSemantics \
  "$proof/V5MerkleUnchangedFullBinaryCapSemantics.lean"
compile "$proof" V5MerkleUnchangedFullReleasedBinaryCap \
  "$proof/V5MerkleUnchangedFullReleasedBinaryCap.lean"
compile "$proof" V5MerkleUnchangedFullSectionNodeClosure \
  "$proof/V5MerkleUnchangedFullSectionNodeClosure.lean"
compile "$proof" V5MerkleUnchangedFullSectionCallBridge \
  "$proof/V5MerkleUnchangedFullSectionCallBridge.lean"
compile "$proof" V5MerkleUnchangedDriverProof \
  "$proof/V5MerkleUnchangedDriverProof.lean"
compile "$proof" V5MerkleUnchangedGeneratedSectionBridge \
  "$proof/V5MerkleUnchangedGeneratedSectionBridge.lean"
compile "$proof" V5MerkleUnchangedFiveSectionComposition \
  "$proof/V5MerkleUnchangedFiveSectionComposition.lean"
compile "$proof" V5MerkleUnchangedPublicAcceptanceBridge \
  "$proof/V5MerkleUnchangedPublicAcceptanceBridge.lean"

if scan '(sorry|admit|native_decide|unsafe|ofReduceBool)' \
    "$generated/V5MerkleUnchangedFull/TypesExternal.lean" \
    "$generated/V5MerkleUnchangedFull/Types.lean" \
    "$generated/V5MerkleUnchangedFull/FunsExternal.lean" \
    "$generated/V5MerkleUnchangedFull/Funs.lean" \
    "$proof/V5MerkleExternalSemantics.lean" \
    "$proof"/*.lean; then
  echo "forbidden proof token" >&2
  exit 1
fi

if scan '^axiom ' \
    "$generated/V5MerkleUnchangedFull/TypesExternal.lean" \
    "$generated/V5MerkleUnchangedFull/FunsExternal.lean"; then
  echo "unexpected external axiom" >&2
  exit 1
fi

if scan 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden proof shortcut in Lean output" >&2
  exit 1
fi

echo "Lean 4.32 unchanged V5 Merkle external-semantics replay: PASS"
echo "V5_MERKLE_EXTERNALS_OUT=$out"
echo "log: $log"
