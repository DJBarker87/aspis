#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly generated="$bundle/generated"
readonly proof="$bundle/proof"
readonly lean_bin="${LEAN432_BIN:-$(command -v lean)}"
readonly aeneas_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the patched Aeneas Lean 4.32 library}"
readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly formal_build_root="${ASPIS_FORMAL_BUILD_ROOT:-$root}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"

check_blob() {
  local expected=$1
  local path=$2
  local actual
  actual=$(git -C "$root" hash-object "$path")
  if [[ "$actual" != "$expected" ]]; then
    echo "source identity mismatch: $path" >&2
    echo "expected $expected" >&2
    echo "actual   $actual" >&2
    exit 1
  fi
}

case "$($lean_bin --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac
case "$(rustc +nightly-2026-06-01 --version)" in
  "rustc 1.98.0-nightly (14210df0e 2026-05-31)") ;;
  *) echo "expected Rust nightly-2026-06-01" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lib/Aeneas/Std.olean" ]]
[[ -f "$aeneas_lib/Aeneas/Tactic/RustAttributes.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]

# These identities make the checked extraction release-specific.  In
# particular, changing either verifier source file requires regenerating and
# reviewing this bundle rather than silently replaying an old snapshot.
check_blob a28ff94de05265102ca819849805a7f73c675800 \
  crates/aspis-core/src/field.rs
check_blob 200110100abc81e9cc8b30701744dc985cabba48 \
  crates/aspis-core/src/sumcheck.rs
check_blob cbe62500353df776318fcb8933bc1c2200097ade \
  programs/aspis-verifier/src/v5_relation_stress.rs
check_blob ca28d560e44e5e82e689321f32289831c889a0bd \
  programs/aspis-verifier/src/v5_cu_probe.rs
check_blob 8efce11aa289540a092e33f0b2278e7e9828d98d \
  aeneas-verif/v5-relation-acceptance-20260815/harness/Cargo.toml
check_blob e0dd0073eec123ba6ac8cc56f19994d3896bce5c \
  aeneas-verif/v5-relation-acceptance-20260815/harness/Cargo.lock
check_blob 36c859d6b69489056bff3fd7d9d7c2c5b01f053d \
  aeneas-verif/v5-relation-acceptance-20260815/harness/src/lib.rs
check_blob f2b3e15ccc4f852cdb51ea87c7788d5ef000cd3c \
  aeneas-verif/v5-relation-acceptance-20260815/production-harness/Cargo.toml
check_blob f0dbf1fafc3c391d5a3e467657ce6fb402c8d528 \
  aeneas-verif/v5-relation-acceptance-20260815/production-harness/Cargo.lock
check_blob 391c5cb9f78e7d7c098d6fe9aee162d4814ffe76 \
  aeneas-verif/v5-relation-acceptance-20260815/production-harness/src/lib.rs

if [[ -n "${V5_RELATION_ACCEPTANCE_REPLAY_OUT:-}" ]]; then
  out=$V5_RELATION_ACCEPTANCE_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-relation-acceptance.XXXXXX)
fi
readonly out
readonly log="$out/replay.log"
readonly olean_out="$out/olean"
readonly decoder_out="$out/decoder"
mkdir -p "$olean_out/AspisFormal" "$decoder_out/V5FriDecoderGenerated"
: > "$log"

normalize_generated() {
  local source=$1
  local destination=$2
  perl -0777 -pe '
    # Lean 4.32 uses the split Aeneas imports.  The pinned translator also
    # emits signed annotations for two wrapping-shift literals whose Rust
    # callee signature is u32; canonicalize those annotations only.
    s/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n/;
    s{Source: '\''[^'\''\n]*/(crates|programs)/}{Source: '\''$1/}g;
    s/(wrapping_shr\s+[^\n]*?)\s+([13])#i32/$1 $2#u32/g;
  ' "$source" > "$destination"
}

compare_generated() {
  local regenerated=$1
  local checked=$2
  local name=$3
  local checked_normalized="$out/$name.checked.lean"
  local regenerated_normalized="$out/$name.regenerated.lean"
  normalize_generated "$checked" "$checked_normalized"
  normalize_generated "$regenerated" "$regenerated_normalized"
  if ! cmp -s "$checked_normalized" "$regenerated_normalized"; then
    echo "regenerated Lean differs: $name" >&2
    diff -u "$checked_normalized" "$regenerated_normalized" | sed -n '1,160p' || true
    exit 1
  fi
  echo "MATCH $name" | tee -a "$log"
}

extract_kernel() {
  local name=$1
  local start=$2
  local namespace=$3
  local raw_file=$4
  local checked_file=$5
  shift 5
  local llbc="$out/$name.llbc"
  local raw_dir="$out/$name-raw"
  mkdir -p "$raw_dir"
  echo "EXTRACT $name" | tee -a "$log"
  (
    cd "$harness"
    CARGO_TARGET_DIR="$out/cargo-$name" "$charon_bin" cargo \
      --preset aeneas --start-from "$start" "$@" \
      --dest-file "$llbc" -- --release --locked
  ) >> "$log" 2>&1
  echo "TRANSLATE $name" | tee -a "$log"
  "$aeneas_bin" -backend lean -namespace "$namespace" -dest "$raw_dir" \
    -max-heartbeats 800000 -max-recdepth 3000 "$llbc" >> "$log" 2>&1
  compare_generated "$raw_dir/$raw_file" "$checked_file" "$name"
}

# These five roots are accepted directly by the pinned tools.  They are
# regenerated from the current Rust and compared definition-for-definition
# with the checked Lean snapshots.
extract_kernel boundary \
  v5_relation_acceptance_harness::extract_boundary_sum \
  V5RelationBoundaryGenerated Boundary.lean \
  "$generated/V5RelationBoundaryGenerated.lean" \
  --include aspis_core::field --include aspis_core::sumcheck

extract_kernel evaluate \
  v5_relation_acceptance_harness::extract_evaluate \
  V5RelationEvaluateGenerated Evaluate.lean \
  "$generated/V5RelationEvaluateGenerated.lean" \
  --include aspis_core::field --include aspis_core::sumcheck

extract_kernel decode \
  v5_relation_acceptance_harness::relation_stress::decode_indexed \
  V5RelationDecodeGenerated Decode.lean \
  "$generated/V5RelationDecodeGenerated.lean" \
  --include aspis_core::field --include aspis_core::sumcheck

extract_kernel layout \
  v5_relation_acceptance_harness::extract_relation_layout \
  V5RelationLayoutGenerated Layout.lean \
  "$generated/V5RelationLayoutGenerated.lean" \
  --include aspis_core::sumcheck::SUMCHECK_COEFFICIENTS

# `weight_at` is deliberately opaque in this extraction because the pinned
# Aeneas translator fails inside that generic helper.  The complete dot body
# and its production dispatch remain generated; the resulting declaration is
# visible in the proof's printed axiom list.
extract_kernel main-dot-opaque \
  v5_relation_acceptance_harness::extract_weight_dot \
  V5RelationMainDotGenerated Main-dot-opaque.lean \
  "$generated/V5RelationMainDotGenerated.lean" \
  --include aspis_core::field --include aspis_core::sumcheck \
  --opaque 'aspis_core::sumcheck::_::weight_at'

formal_path=$(cd "$formal_build_root/AspisFormal" && \
  NO_DNA=1 lake env printenv LEAN_PATH)
readonly formal_path

# Lean resolves modules in one package directory.  Seed the isolated output
# with the already-built, unchanged AspisFormal modules before replacing the
# new relation-security chain with freshly compiled objects from this checkout.
formal_olean_root=""
IFS=: read -r -a formal_path_entries <<< "$formal_path"
for entry in "${formal_path_entries[@]}"; do
  if [[ -f "$entry/AspisFormal/V5ComponentCQM31Representation.olean" ]]; then
    formal_olean_root=$entry
    break
  fi
done
if [[ -z "$formal_olean_root" ]]; then
  echo "no built AspisFormal dependency tree found" >&2
  echo "run lake build or set ASPIS_FORMAL_BUILD_ROOT to a built checkout" >&2
  exit 1
fi
cp -R "$formal_olean_root/AspisFormal/." "$olean_out/AspisFormal/"

compile() {
  local target=$1
  local source=$2
  echo "COMPILE $target" >> "$log"
  LEAN_PATH="$olean_out:$decoder_out:$formal_path:$aeneas_lib" \
    "$lean_bin" -j 1 -o "$olean_out/$target.olean" "$source" >> "$log" 2>&1
}

# Rebuild the maintained source-shaped relation model from this checkout.
# Earlier, unchanged AspisFormal modules and mathlib are resolved through the
# selected build root; every module in this new dependency chain is rebuilt
# into the isolated output directory.
for module in \
  V5MerkleAuthenticationBinding \
  V5MerkleRustBridge \
  V5MerkleConsumedValueBridge \
  V5RelationSumcheckSoundness \
  V5FriRelationCandidateBridge \
  V5Tag67RelationListInclusion \
  V5Tag67FalseAcceptanceDecomposition \
  V5Tag67ModeledRelationAcceptanceBridge \
  V5RelationStressSourceBridge
do
  compile "AspisFormal/$module" "$root/AspisFormal/AspisFormal/$module.lean"
done

# Rebuild the already extracted production QM31 decoder used by the 58-field
# relation-tail theorem.
readonly decoder_bundle="$root/aeneas-verif/v5-fri-byte-decoders-20260814"
compile_decoder() {
  local target=$1
  local source=$2
  echo "COMPILE $target" >> "$log"
  LEAN_PATH="$decoder_out:$olean_out:$formal_path:$aeneas_lib" \
    "$lean_bin" -j 1 -o "$decoder_out/$target.olean" "$source" >> "$log" 2>&1
}
compile_decoder V5FriDecoderGenerated/Types \
  "$decoder_bundle/generated/V5FriDecoderGenerated/Types.lean"
compile_decoder V5FriDecoderGenerated/FunsExternal \
  "$decoder_bundle/generated/V5FriDecoderGenerated/FunsExternal.lean"
compile_decoder V5FriDecoderGenerated/Funs \
  "$decoder_bundle/generated/V5FriDecoderGenerated/Funs.lean"
compile_decoder V5FriDecoderProof "$decoder_bundle/proof/V5FriDecoderProof.lean"

for source in "$generated"/*.lean; do
  module=$(basename "$source" .lean)
  compile "$module" "$source"
done

compile V5RelationAcceptanceSourceProof \
  "$proof/V5RelationAcceptanceSourceProof.lean"
compile V5RelationCompactFoldKernelProof \
  "$proof/V5RelationCompactFoldKernelProof.lean"
compile V5RelationRoundKernelProof \
  "$proof/V5RelationRoundKernelProof.lean"
compile V5RelationTailDecoderProof \
  "$proof/V5RelationTailDecoderProof.lean"
compile V5RelationTerminalKernelProof \
  "$proof/V5RelationTerminalKernelProof.lean"

if rg -n '\b(sorry|admit|native_decide|unsafe|ofReduceBool)\b' \
    "$proof" "$root/AspisFormal/AspisFormal/V5RelationStressSourceBridge.lean"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if rg -n 'sorryAx|ofReduceBool' "$log"; then
  echo "forbidden axiom in relation-acceptance proof replay" >&2
  exit 1
fi

echo "Lean 4.32 V5 relation-acceptance extraction and proof replay: PASS"
echo "V5_RELATION_ACCEPTANCE_REPLAY_OUT=$out"
echo "log: $log"
