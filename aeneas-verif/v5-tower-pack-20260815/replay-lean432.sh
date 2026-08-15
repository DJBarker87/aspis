#!/usr/bin/env bash
set -euo pipefail

readonly bundle="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly root="$(cd "$bundle/../.." && pwd -P)"
readonly harness="$bundle/harness"
readonly checked_generated="$bundle/generated/V5TowerPack"
readonly checked_proof="$bundle/proof/V5TowerPackGeneratedProof.lean"
readonly exact_tower_module="$root/AspisFormal/AspisFormal/V5ExactTowerPacking.lean"
readonly shared_generated="$root/aeneas-verif/proof/AspisCoreFieldReduceU64.lean"
readonly shared_proof="$root/aeneas-verif/proof/M31ReduceU64Proof.lean"

readonly charon_repo="${ASPIS_CHARON_REPO:?set ASPIS_CHARON_REPO to pinned Charon cb50ff16}"
readonly aeneas_repo="${ASPIS_AENEAS_REPO:?set ASPIS_AENEAS_REPO to pinned Aeneas b59d5188}"
readonly aeneas_lean_lib="${AENEAS_LEAN_LIB:?set AENEAS_LEAN_LIB to the Lean-4.32 Aeneas library directory}"
readonly charon_bin="${CHARON_BIN:-$charon_repo/bin/charon}"
readonly aeneas_bin="${AENEAS_BIN:-$aeneas_repo/bin/aeneas}"

readonly expected_charon_commit="cb50ff16b9f1066b8a97dc06da704de2da2fa41c"
readonly expected_aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly expected_field_blob="a28ff94de05265102ca819849805a7f73c675800"
readonly expected_harness_toml_blob="88655332230dc2c5726fbcabba41a2192b244e33"
readonly expected_harness_lock_blob="6ea06f0ab42b0c92983e17c8a2ce801ff654d398"
readonly expected_shared_generated_blob="543f2933460cf9f9c2e09995981b6e2da3968e0c"
readonly expected_shared_proof_blob="6f02d83d3816d6b697008bb62af9e59ec5d29c37"
readonly expected_checked_proof_blob="f2a27c5486028314aa7e01aa1e11ec89314d6124"
readonly expected_exact_tower_module_blob="2a4ee0134a3dbb37ebfb437c177ad16943953703"
readonly expected_types_semantic_sha256="cada23451010c762751611eed730dbf503207606f93e374bb4d9c1028c7028f3"
readonly expected_funs_semantic_sha256="cc6f1736037a1dc676b1077131f17c602a973545aa82650e204d5cd5fdbd5963"

if [[ -n "${LEAN432_BIN:-}" ]]; then
  lean_cmd=("$LEAN432_BIN")
elif command -v elan >/dev/null 2>&1; then
  lean_cmd=(elan run leanprover/lean4:v4.32.0 lean)
else
  lean_cmd=("$(command -v lean)")
fi
readonly -a lean_cmd

case "$("${lean_cmd[@]}" --version)" in
  "Lean (version 4.32.0,"*) ;;
  *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
esac

[[ -x "$charon_bin" ]]
[[ -x "$aeneas_bin" ]]
[[ -f "$aeneas_lean_lib/Aeneas/Std.olean" ]]
[[ "$(git -C "$charon_repo" rev-parse HEAD)" == "$expected_charon_commit" ]]
[[ "$(git -C "$aeneas_repo" rev-parse HEAD)" == "$expected_aeneas_commit" ]]
[[ "$(git -C "$root" hash-object crates/aspis-core/src/field.rs)" == \
  "$expected_field_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.toml")" == \
  "$expected_harness_toml_blob" ]]
[[ "$(git -C "$root" hash-object "$harness/Cargo.lock")" == \
  "$expected_harness_lock_blob" ]]
[[ "$(git -C "$root" hash-object "$shared_generated")" == \
  "$expected_shared_generated_blob" ]]
[[ "$(git -C "$root" hash-object "$shared_proof")" == \
  "$expected_shared_proof_blob" ]]
[[ "$(git -C "$root" hash-object "$checked_proof")" == \
  "$expected_checked_proof_blob" ]]
[[ "$(git -C "$root" hash-object "$exact_tower_module")" == \
  "$expected_exact_tower_module_blob" ]]

if [[ -n "${V5_TOWER_PACK_REPLAY_OUT:-}" ]]; then
  out=$V5_TOWER_PACK_REPLAY_OUT
  mkdir -p "$out"
  [[ -z "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]
else
  out=$(mktemp -d /private/tmp/v5-tower-pack.XXXXXX)
fi
readonly out
readonly llbc="$out/V5TowerPack.llbc"
readonly raw="$out/raw"
readonly checked_src="$out/checked-src"
readonly olean_root="$out/olean"
readonly extract_log="$out/extract.log"
readonly aeneas_log="$out/aeneas.log"
readonly lean_log="$out/lean432.log"
mkdir -p "$raw" "$checked_src/V5TowerPack" "$olean_root/V5TowerPack"
: > "$extract_log"
: > "$aeneas_log"
: > "$lean_log"

(
  cd "$harness"
  CARGO_TARGET_DIR="$out/cargo-target" "$charon_bin" cargo \
    --preset aeneas \
    --start-from \
      'aspis_core_tower_pack_extraction::field::qm31_pack_base4' \
    --dest-file "$llbc" -- --release --locked
) >> "$extract_log" 2>&1

"$charon_bin" pretty-print "$llbc" > "$out/V5TowerPack.llbc.txt"
rg -F 'qm31_pack_base4' "$out/V5TowerPack.llbc.txt" >/dev/null
rg -F 'reduce_u64' "$out/V5TowerPack.llbc.txt" >/dev/null
rg -F 'copy_from_slice' "$out/V5TowerPack.llbc.txt" >/dev/null

"$aeneas_bin" -backend lean -namespace V5TowerPackGenerated \
  -split-files -no-progress-bar \
  -dest "$raw" "$llbc" > "$aeneas_log" 2>&1

normalize_types() {
  perl -0777 -pe \
    's/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n/; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

normalize_funs() {
  perl -0777 -pe \
    's/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n/; s{/-.*?-/}{}gs; s{--[^\n]*}{}g; s/\s+//g' \
    "$1"
}

normalize_types "$raw/Types.lean" > "$out/raw.Types.semantic"
normalize_types "$checked_generated/Types.lean" > "$out/checked.Types.semantic"
normalize_funs "$raw/Funs.lean" > "$out/raw.Funs.semantic"
normalize_funs "$checked_generated/Funs.lean" > "$out/checked.Funs.semantic"

cmp "$out/raw.Types.semantic" "$out/checked.Types.semantic"
cmp "$out/raw.Funs.semantic" "$out/checked.Funs.semantic"
[[ "$(shasum -a 256 "$out/raw.Types.semantic" | awk '{print $1}')" == \
  "$expected_types_semantic_sha256" ]]
[[ "$(shasum -a 256 "$out/raw.Funs.semantic" | awk '{print $1}')" == \
  "$expected_funs_semantic_sha256" ]]

# The old shared reducer extraction imports Aeneas's umbrella module.  The
# Lean-4.32 checked copy uses the narrower modules; this changes imports only.
perl -0777 -pe \
  's/import Aeneas\n/import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n/' \
  "$shared_generated" > "$checked_src/AspisCoreFieldReduceU64.lean"
cp "$checked_generated/Types.lean" "$checked_src/V5TowerPack/Types.lean"
cp "$checked_generated/Funs.lean" "$checked_src/V5TowerPack/Funs.lean"
cp "$shared_proof" "$checked_src/M31ReduceU64Proof.lean"
cp "$checked_proof" "$checked_src/V5TowerPackGeneratedProof.lean"

aspis_path=${ASPIS_LEAN_PATH:-$(
  cd "$root/AspisFormal" && NO_DNA=1 lake env printenv LEAN_PATH
)}
export LEAN_PATH="$olean_root:$checked_src:$aeneas_lean_lib:$aspis_path"

(
  cd "$root/AspisFormal"
  NO_DNA=1 lake build AspisFormal.V5ExactTowerPacking
) >> "$lean_log" 2>&1

(
  cd "$checked_src"
  "${lean_cmd[@]}" -j 1 \
    -o "$olean_root/V5TowerPack/Types.olean" \
    V5TowerPack/Types.lean
  "${lean_cmd[@]}" -j 1 \
    -o "$olean_root/V5TowerPack/Funs.olean" \
    V5TowerPack/Funs.lean
  "${lean_cmd[@]}" -j 1 \
    -o "$olean_root/AspisCoreFieldReduceU64.olean" \
    AspisCoreFieldReduceU64.lean
  "${lean_cmd[@]}" -j 1 \
    -o "$olean_root/M31ReduceU64Proof.olean" \
    M31ReduceU64Proof.lean
  "${lean_cmd[@]}" -j 1 \
    -o "$out/V5TowerPackGeneratedProof.olean" \
    V5TowerPackGeneratedProof.lean
) >> "$lean_log" 2>&1

if rg -n '\b(sorry|admit|native_decide|axiom|unsafe|ofReduceBool)\b' \
    "$checked_generated" "$checked_proof" "$exact_tower_module" \
    "$shared_generated" "$shared_proof"; then
  echo "forbidden proof token" >&2
  exit 1
fi
if rg -n "declaration uses 'sorry'|declaration has metavariables" "$lean_log"; then
  echo "incomplete declaration in tower-packing proof" >&2
  exit 1
fi
# The dependency audit below parses each `#print axioms` result and rejects
# every name outside the standard allowlist, including `sorryAx` and
# `Lean.ofReduceBool`.  Do not grep those words globally: imported module
# documentation may mention them while explaining that its theorems do not
# depend on them.
if ! awk '
  / depends on axioms: \[/ { active = 1; sub(/^.*\[/, "") }
  active {
    line = $0
    gsub(/propext|Classical\.choice|Quot\.sound/, "", line)
    gsub(/[\[\],[:space:]]/, "", line)
    if (line != "") { print "unexpected axiom: " line; bad = 1 }
    if ($0 ~ /\]/) active = 0
  }
  END { exit bad }
' "$lean_log"; then
  exit 1
fi

echo "Release-mode qm31_pack_base4 extraction: MATCH"
echo "Four canonical M31 inputs map exactly to (1,i,u,i*u): PASS"
echo "V5_TOWER_PACK_REPLAY_OUT=$out"
echo "extraction log: $extract_log"
echo "Lean log: $lean_log"
