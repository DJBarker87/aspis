#!/usr/bin/env bash
set -euo pipefail

readonly aeneas_commit="b59d5188c082f704a418c7cb4e52ad69328002d1"
readonly aeneas_url="https://github.com/AeneasVerif/aeneas.git"
readonly patch_sha256="04e9c2cf33d941b8e8959c9bc4b27607164e69a5d182377d8708b59f9eca2dc4"
readonly manifest_sha256="5d15524cf34ff705bebbd037e80baec63683d5d5a3a37a539a62f17405a2fc62"

readonly script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly verification_dir="$(cd "$script_dir/.." && pwd -P)"
readonly harness_dir="$verification_dir/lean432"
readonly patch_file="$harness_dir/aeneas-b59d5188-lean432.patch"
readonly manifest_file="$harness_dir/lake-manifest.json"
readonly patched_hashes="$harness_dir/patched-aeneas-hashes.sha256"

for command_name in git jq lake; do
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "missing required command: $command_name" >&2
    exit 2
  fi
done

sha256_of() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

require_sha256() {
  local expected=$1
  local file=$2
  local actual
  actual=$(sha256_of "$file")
  if [[ "$actual" != "$expected" ]]; then
    echo "SHA-256 mismatch for $file: expected $expected, got $actual" >&2
    exit 1
  fi
}

require_sha256 "$patch_sha256" "$patch_file"
require_sha256 "$manifest_sha256" "$manifest_file"

if [[ -n "${AENEAS_LEAN432_OUT:-}" ]]; then
  out=$AENEAS_LEAN432_OUT
  mkdir -p "$out"
  if [[ -n "$(find "$out" -mindepth 1 -maxdepth 1 -print -quit)" ]]; then
    echo "AENEAS_LEAN432_OUT must be empty: $out" >&2
    exit 2
  fi
else
  out=$(mktemp -d "${RUNNER_TEMP:-${TMPDIR:-/tmp}}/aspis-aeneas-lean432.XXXXXX")
fi
readonly out
readonly checkout="$out/aeneas"
readonly backend="$checkout/backends/lean"
readonly source_repo="${ASPIS_AENEAS_432_SOURCE:-$aeneas_url}"

git clone --quiet --no-local --no-checkout "$source_repo" "$checkout"
git -C "$checkout" checkout --quiet --detach "$aeneas_commit"
if [[ "$(git -C "$checkout" rev-parse HEAD)" != "$aeneas_commit" ]]; then
  echo "Aeneas checkout did not resolve to the pinned commit" >&2
  exit 1
fi

git -C "$checkout" apply --check --unidiff-zero "$patch_file"
git -C "$checkout" apply --unidiff-zero "$patch_file"
git -C "$checkout" diff --check

readonly expected_patch_files=$'backends/lean/Aeneas/Tactic/Simproc/ReduceZMod/ReduceZMod.lean\nbackends/lean/AeneasMeta/BvEnumToBitVec.lean\nbackends/lean/AeneasMeta/Simp/Simp.lean\nbackends/lean/lakefile.lean\nbackends/lean/lean-toolchain'
readonly actual_patch_files="$(git -C "$checkout" diff --name-only | LC_ALL=C sort)"
if [[ "$actual_patch_files" != "$expected_patch_files" ]]; then
  echo "Lean 4.32 compatibility patch changed unexpected files" >&2
  printf '%s\n' "$actual_patch_files" >&2
  exit 1
fi

(
  cd "$checkout"
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum -c "$patched_hashes"
  else
    shasum -a 256 -c "$patched_hashes"
  fi
)

cp "$manifest_file" "$backend/lake-manifest.json"
cp "$manifest_file" "$out/lake-manifest.before.json"

if [[ "$(jq -r '.packages[] | select(.name == "mathlib") | .rev' "$backend/lake-manifest.json")" != "81a5d257c8e410db227a6665ed08f64fea08e997" ]]; then
  echo "Aeneas manifest does not pin the audited mathlib commit" >&2
  exit 1
fi

(
  cd "$backend"
  case "$(lake env lean --version)" in
    "Lean (version 4.32.0,"*) ;;
    *) echo "expected Lean 4.32.0" >&2; exit 1 ;;
  esac
  lake build Aeneas.Std Aeneas.Tactic.RustAttributes
  cmp lake-manifest.json "$out/lake-manifest.before.json"
)

readonly lean_lib="$backend/.lake/build/lib/lean"
if [[ ! -f "$lean_lib/Aeneas/Std.olean" ]] ||
    [[ ! -f "$lean_lib/Aeneas/Tactic/RustAttributes.olean" ]]; then
  echo "pinned Aeneas Lean library did not build completely" >&2
  exit 1
fi

readonly lean_path="$(cd "$backend" && lake env printenv LEAN_PATH)"
echo "Pinned Aeneas Lean 4.32 library: PASS"
echo "AENEAS_LEAN432_OUT=$out"
echo "AENEAS_LEAN_LIB=$lean_lib"

if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
  printf 'aeneas_lean432_out=%s\n' "$out" >> "$GITHUB_OUTPUT"
  printf 'aeneas_lean_lib=%s\n' "$lean_lib" >> "$GITHUB_OUTPUT"
  printf 'aeneas_lean_path=%s\n' "$lean_path" >> "$GITHUB_OUTPUT"
fi
