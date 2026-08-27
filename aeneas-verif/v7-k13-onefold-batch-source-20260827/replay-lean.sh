#!/usr/bin/env bash
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${AENEAS_LEAN_BACKEND:?set AENEAS_LEAN_BACKEND to the Aeneas Lean backend}"

test -f "$AENEAS_LEAN_BACKEND/lakefile.lean" -o \
  -f "$AENEAS_LEAN_BACKEND/lakefile.toml"
work_tmp=$(mktemp -d "$AENEAS_LEAN_BACKEND/aspis-v7-k13-source.XXXXXX")
cleanup() {
  case "$work_tmp" in
    "$AENEAS_LEAN_BACKEND"/aspis-v7-k13-source.*) rm -rf -- "$work_tmp" ;;
    *) echo "refusing unsafe cleanup target: $work_tmp" >&2 ;;
  esac
}
trap cleanup EXIT

cp -R "$script_dir/generated/V7K13FoldResidual" "$work_tmp/"
cp -R "$script_dir/generated/V7K13AddBatch" "$work_tmp/"
cp "$script_dir/proof/V7K13FoldedValuesTrace.lean" "$work_tmp/"
cp "$script_dir/proof/V7K13ShiftedResidualTrace.lean" "$work_tmp/"
cp "$script_dir/proof/V7K13QueryBatchInsertionTrace.lean" "$work_tmp/"

export LEAN_NUM_THREADS=1
export LEAN_PATH="$work_tmp:$AENEAS_LEAN_BACKEND/.lake/build/lib/lean"

compile() {
  source_file=$1
  output_file=${source_file%.lean}.olean
  (cd "$AENEAS_LEAN_BACKEND" &&
    lake env lean -j1 -o "$output_file" "$source_file")
}

compile "$work_tmp/V7K13FoldResidual/Types.lean"
compile "$work_tmp/V7K13FoldResidual/FunsExternal.lean"
compile "$work_tmp/V7K13FoldResidual/Funs.lean"
compile "$work_tmp/V7K13FoldedValuesTrace.lean"
compile "$work_tmp/V7K13ShiftedResidualTrace.lean"

compile "$work_tmp/V7K13AddBatch/TypesExternal.lean"
compile "$work_tmp/V7K13AddBatch/Types.lean"
compile "$work_tmp/V7K13AddBatch/FunsExternal.lean"
compile "$work_tmp/V7K13AddBatch/Funs.lean"
compile "$work_tmp/V7K13QueryBatchInsertionTrace.lean"

echo 'V7 K1.3 shifted query-batch Lean source replay: PASS'
