#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
package_dir=$(CDPATH= cd -- "$script_dir/.." && pwd)
repo_root=$(git -C "$package_dir" rev-parse --show-toplevel)
deployed_commit=1589706d38a5e8ca705fbf7aaed2c82cf8595510
transcript_path=crates/aspis-core/src/v6_transcript.rs
sumcheck_path=crates/aspis-core/src/sumcheck.rs
field_path=crates/aspis-core/src/field.rs
certificate_file="$script_dir/SOURCE-TRANSFORM-CERTIFICATE.tsv"

output_dir="$script_dir/source-blobs"
mkdir -p "$output_dir"

git -C "$repo_root" show "$deployed_commit:$transcript_path" \
  > "$output_dir/v6_transcript.original.rs"
cp "$output_dir/v6_transcript.original.rs" \
  "$output_dir/v6_transcript.unrolled.rs"
git -C "$repo_root" show "$deployed_commit:$sumcheck_path" \
  > "$output_dir/sumcheck.original.rs"
cp "$output_dir/sumcheck.original.rs" \
  "$output_dir/sumcheck.indexed.rs"
git -C "$repo_root" show "$deployed_commit:$field_path" \
  > "$output_dir/field.original.rs"
cp "$output_dir/field.original.rs" \
  "$output_dir/field.indexed.rs"

temporary_tree=$(mktemp -d "${TMPDIR:-/tmp}/aspis-tag73-source-transform.XXXXXX")
cleanup() {
  case "$temporary_tree" in
    "${TMPDIR:-/tmp}"/aspis-tag73-source-transform.*)
      rm -rf -- "$temporary_tree"
      ;;
    *)
      echo "refusing unsafe source-transform cleanup: $temporary_tree" >&2
      ;;
  esac
}
trap cleanup EXIT

mkdir -p "$temporary_tree/crates/aspis-core/src"
cp "$output_dir/v6_transcript.unrolled.rs" \
  "$temporary_tree/$transcript_path"
cp "$output_dir/sumcheck.indexed.rs" \
  "$temporary_tree/$sumcheck_path"
cp "$output_dir/field.indexed.rs" \
  "$temporary_tree/$field_path"

exec 3< "$certificate_file"
verify_stage() {
  stage=$1
  if ! IFS=$'\t' read -r expected_stage expected_transcript \
      expected_sumcheck expected_field <&3; then
    echo "missing source-transform certificate row: $stage" >&2
    exit 1
  fi
  test "$expected_stage" = "$stage"
  actual_transcript=$(sha256sum "$temporary_tree/$transcript_path" | cut -d ' ' -f 1)
  actual_sumcheck=$(sha256sum "$temporary_tree/$sumcheck_path" | cut -d ' ' -f 1)
  actual_field=$(sha256sum "$temporary_tree/$field_path" | cut -d ' ' -f 1)
  test "$actual_transcript" = "$expected_transcript"
  test "$actual_sumcheck" = "$expected_sumcheck"
  test "$actual_field" = "$expected_field"
  printf 'source-transform stage %s: PASS %s %s %s\n' \
    "$stage" "$actual_transcript" "$actual_sumcheck" "$actual_field"
}

verify_stage 00-original
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/unroll-fixed-relation-rounds.patch"
verify_stage 01-unroll-fixed-relation-rounds
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/index-line-batch-zip.patch"
verify_stage 02-index-line-batch-zip
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/lambda-lift-terminal-line.patch"
verify_stage 03-lambda-lift-terminal-line
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/lambda-lift-terminal-batch.patch"
verify_stage 04-lambda-lift-terminal-batch
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/lambda-lift-terminal-contributions.patch"
verify_stage 05-lambda-lift-terminal-contributions
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/lambda-lift-terminal-components.patch"
verify_stage 06-lambda-lift-terminal-components
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/lambda-lift-terminal-component-match.patch"
verify_stage 07-lambda-lift-terminal-component-match
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/index-terminal-deferred-max.patch"
verify_stage 08-index-terminal-deferred-max
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/index-terminal-component-loops.patch"
verify_stage 09-index-terminal-component-loops
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/lambda-lift-terminal-line-component.patch"
verify_stage 10-lambda-lift-terminal-line-component
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/specialize-terminal-dot-log2.patch"
verify_stage 11-specialize-terminal-dot-log2
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/unroll-qm31-dot3-row-lengths.patch"
verify_stage 12-unroll-qm31-dot3-row-lengths
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/bind-indexed-qm31-dot3.patch"
verify_stage 13-bind-indexed-qm31-dot3
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/name-wire-map-adapter.patch"
verify_stage 14-name-wire-map-adapter
patch --silent -d "$temporary_tree" -p1 \
  < "$script_dir/stage-finish-round-tail.patch"
verify_stage 15-stage-finish-round-tail
if IFS= read -r extra_certificate_row <&3; then
  echo "unexpected source-transform certificate row: $extra_certificate_row" >&2
  exit 1
fi
exec 3<&-
cp "$temporary_tree/$transcript_path" \
  "$output_dir/v6_transcript.unrolled.rs"
cp "$temporary_tree/$sumcheck_path" \
  "$output_dir/sumcheck.indexed.rs"
cp "$temporary_tree/$field_path" \
  "$output_dir/field.indexed.rs"

test "$(sha256sum "$output_dir/v6_transcript.original.rs" | awk '{print $1}')" = \
  8422e8fa817fae3a7db01976725fcfd3642ea837f4e87366829f63309c6f28d3
test "$(sha256sum "$output_dir/sumcheck.original.rs" | awk '{print $1}')" = \
  9cb353d5640d00717f0fbe4c46b2870597602774abe6e47ce73e04b25fb48bd7
test "$(sha256sum "$output_dir/field.original.rs" | awk '{print $1}')" = \
  e118899472e3049db688573570296f06696be659524bbf6a62ace537f0316312
test "$(rg -n '^    for round in 1\.\.V6_RELATION_ROUNDS \{' \
  "$output_dir/v6_transcript.original.rs" | wc -l | tr -d ' ')" = 1
test "$(rg -n '^    for round in 1\.\.V6_RELATION_ROUNDS \{' \
  "$output_dir/v6_transcript.unrolled.rs" | wc -l | tr -d ' ')" = 0

(
  cd "$output_dir"
  sha256sum \
    v6_transcript.original.rs \
    v6_transcript.unrolled.rs \
    sumcheck.original.rs \
    sumcheck.indexed.rs \
    field.original.rs \
    field.indexed.rs
)
